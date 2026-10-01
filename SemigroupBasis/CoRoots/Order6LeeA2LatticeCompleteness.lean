import SemigroupBasis.CoRoots.Order6LeeA2LatticeScaffold
import SemigroupBasis.CoRoots.S5_107BlockCombinatorics

namespace SemigroupBasis.CoRoots.Order6LeeA2LatticeScaffold

open SemigroupBasis

private theorem leeA2Head_mem_toList (word : Word Nat) :
    word.head ∈ word.toList := by
  cases word
  simp [Word.toList]

private theorem leeA2Final_mem_toList (word : Word Nat) :
    word.final ∈ word.toList := by
  cases word with
  | mk head tail =>
      simpa [Word.final, Word.toList] using
        (List.getLastD_mem_cons (l := tail) (a := head))

/-!
## Prescribed-factor completion

The marked-digraph normalizer already contains the required path-splicing
construction.  The following specialization records the exact form needed
for edge saturation: an arbitrary directed walk, not merely a simple path,
can be exposed as a factor without changing the ambient marked graph.
-/

theorem existsSameMarkedDigraphWithFactor
    (ambient factor : Word Nat)
    (indecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable ambient)
    (factorIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient factor) :
    ∃ exposed : Word Nat,
      ambient.SameMarkedDigraph exposed ∧
        SemigroupBasis.CoRoots.S5_868.OccursAsFactor factor exposed := by
  open SemigroupBasis.CoRoots.S5_868 in
    rcases existsCompletionPathFold ambient indecomposable [factor]
        (by
          intro path member
          have equal : path = factor := by simpa using member
          subst path
          exact factorIn)
        ambient (directedPathIn_refl ambient) with
      ⟨walk, walkHead, walkIn, ambientOccurs, factorOccurs⟩
    have walkFinalMember : walk.final ∈ ambient.toList :=
      walkIn.1 walk.final (leeA2Final_mem_toList walk)
    have ambientFinalMember : ambient.final ∈ ambient.toList :=
      leeA2Final_mem_toList ambient
    rcases indecomposable walk.final walkFinalMember
        ambient.final ambientFinalMember with
      ⟨closing, closingHead, closingFinal, closingIn⟩
    have boundary : walk.final = closing.head :=
      closingHead.symm
    let exposed := completionJoin walk closing
    have exposedIn : DirectedPathIn ambient exposed :=
      completionJoin_directedPathIn boundary walkIn closingIn
    have walkOccurs : OccursAsFactor walk exposed :=
      completionJoin_occurs_left walk closing
    have ambientExposed : OccursAsFactor ambient exposed :=
      occursAsFactor_trans ambientOccurs walkOccurs
    have exposedHead : exposed.head = ambient.head :=
      (completionJoin_head walk closing).trans walkHead
    have exposedFinal : exposed.final = ambient.final :=
      (completionJoin_final boundary).trans closingFinal
    have sameGraph : ambient.SameMarkedDigraph exposed := by
      refine ⟨exposedHead.symm, exposedFinal.symm, ?_, ?_⟩
      · intro letter
        constructor
        · exact occursAsFactor_support ambientExposed letter
        · exact exposedIn.1 letter
      · intro source target
        constructor
        · exact occursAsFactor_edge ambientExposed source target
        · exact exposedIn.2 source target
    exact
      ⟨exposed, sameGraph,
        occursAsFactor_trans
          (factorOccurs factor (by simp)) walkOccurs⟩

private abbrev LeeA2ListDerives :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

/-- Apply the middle-block expansion inside an explicitly located factor.
The target word is returned existentially so no partial list-to-word
conversion enters the statement. -/
theorem derivesMiddleExpansionAtFactor
    (ambient u v : Word Nat) (stem suffix : List Nat)
    (shape :
      ambient.toList =
        stem ++ (((u ++ v) ++ u).toList) ++ suffix) :
    ∃ expanded : Word Nat,
      Derives basis ambient expanded ∧
        expanded.toList =
          stem ++ ((((u ++ v) ++ v) ++ u).toList) ++ suffix := by
  have core :
      LeeA2ListDerives
        (((u ++ v) ++ u).toList)
        ((((u ++ v) ++ v) ++ u).toList) :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesMiddleExpansion u v)
  have contextual :
      LeeA2ListDerives ambient.toList
        (stem ++ ((((u ++ v) ++ v) ++ u).toList) ++ suffix) := by
    simpa [shape] using core.context stem suffix
  cases ambient with
  | mk ambientHead ambientTail =>
      obtain ⟨expandedHead, expandedTail, targetShape, derivation⟩ :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.from_cons contextual
      let expanded :=
        SemigroupBasis.CoRoots.S5_107.listWordOfCons
          expandedHead expandedTail
      refine ⟨expanded, ?_, ?_⟩
      · simpa [expanded,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons] using derivation
      · simpa [expanded,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons] using
          targetShape.symm

theorem middleExpansion_addsClosingEdge (u v : Word Nat) :
    (v.final, v.head) ∈
      ((((u ++ v) ++ v) ++ u).adjacentPairs) := by
  rw [Word.adjacentPairs_append]
  apply List.mem_append.mpr
  left
  rw [Word.adjacentPairs_append]
  apply List.mem_append.mpr
  right
  simp [Word.final_append]

structure BoundarySupportEdgeExtension
    (source target : Word Nat) : Prop where
  sameHead : target.head = source.head
  sameFinal : target.final = source.final
  sameSupport :
    ∀ letter, letter ∈ target.toList ↔ letter ∈ source.toList
  edgeMono :
    ∀ left right,
      (left, right) ∈ source.adjacentPairs ->
        (left, right) ∈ target.adjacentPairs

namespace BoundarySupportEdgeExtension

theorem refl (word : Word Nat) :
    BoundarySupportEdgeExtension word word :=
  ⟨rfl, rfl, fun _ => Iff.rfl, fun _ _ => id⟩

theorem trans
    {first second third : Word Nat}
    (firstSecond : BoundarySupportEdgeExtension first second)
    (secondThird : BoundarySupportEdgeExtension second third) :
    BoundarySupportEdgeExtension first third := by
  refine
    ⟨secondThird.sameHead.trans firstSecond.sameHead,
      secondThird.sameFinal.trans firstSecond.sameFinal, ?_, ?_⟩
  · intro letter
    exact
      (secondThird.sameSupport letter).trans
        (firstSecond.sameSupport letter)
  · intro left right edge
    exact secondThird.edgeMono left right
      (firstSecond.edgeMono left right edge)

end BoundarySupportEdgeExtension

private theorem listAdjacentPairs_append_cons
    (head : Nat) (tail : List Nat) (next : Nat) (suffix : List Nat) :
    SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
        ((head :: tail) ++ next :: suffix) =
      SemigroupBasis.CoRoots.S5_107.listAdjacentPairs (head :: tail) ++
        (tail.getLastD head, next) ::
          SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
            (next :: suffix) :=
  Word.adjacentPairsFrom_append head tail next suffix

private theorem listAdjacentPairs_word (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_107.listAdjacentPairs word.toList =
      word.adjacentPairs := by
  cases word
  rfl

private theorem replaceWord_rightContext_edgeMono
    {old new : Word Nat}
    (sameFinal : new.final = old.final)
    (edgeMono :
      ∀ left right,
        (left, right) ∈ old.adjacentPairs ->
          (left, right) ∈ new.adjacentPairs) :
    ∀ (suffix : List Nat) (left right : Nat),
      (left, right) ∈
          SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
            (old.toList ++ suffix) ->
        (left, right) ∈
          SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
            (new.toList ++ suffix)
  | [], left, right, edge => by
      rw [List.append_nil, listAdjacentPairs_word] at edge ⊢
      exact edgeMono left right edge
  | next :: rest, left, right, edge => by
      rw [show old.toList ++ next :: rest =
        (old.head :: old.tail) ++ next :: rest by rfl,
        listAdjacentPairs_append_cons] at edge
      rw [show new.toList ++ next :: rest =
        (new.head :: new.tail) ++ next :: rest by rfl,
        listAdjacentPairs_append_cons]
      rcases List.mem_append.mp edge with oldEdge | boundaryOrSuffix
      · apply List.mem_append.mpr
        left
        have oldEdge' :
            (left, right) ∈
              SemigroupBasis.CoRoots.S5_107.listAdjacentPairs old.toList := by
          simpa [Word.toList] using oldEdge
        rw [listAdjacentPairs_word] at oldEdge'
        have newEdge := edgeMono left right oldEdge'
        rw [← listAdjacentPairs_word] at newEdge
        simpa [Word.toList] using newEdge
      · apply List.mem_append.mpr
        right
        simp only [List.mem_cons] at boundaryOrSuffix ⊢
        rcases boundaryOrSuffix with boundary | suffixEdge
        · left
          have finalEq :
              new.tail.getLastD new.head =
                old.tail.getLastD old.head := sameFinal
          simpa only [finalEq] using boundary
        · exact Or.inr suffixEdge

private theorem replaceWord_edgeMono
    {old new : Word Nat}
    (sameHead : new.head = old.head)
    (sameFinal : new.final = old.final)
    (edgeMono :
      ∀ left right,
        (left, right) ∈ old.adjacentPairs ->
          (left, right) ∈ new.adjacentPairs) :
    ∀ (stem suffix : List Nat) (left right : Nat),
      (left, right) ∈
          SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
            (stem ++ old.toList ++ suffix) ->
        (left, right) ∈
          SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
            (stem ++ new.toList ++ suffix)
  | [], suffix, left, right, edge => by
      simpa using
        replaceWord_rightContext_edgeMono sameFinal edgeMono
          suffix left right edge
  | stemHead :: stemTail, suffix, left, right, edge => by
      rw [show (stemHead :: stemTail) ++ old.toList ++ suffix =
        (stemHead :: stemTail) ++
          old.head :: (old.tail ++ suffix) by
            simp [Word.toList, List.append_assoc],
        listAdjacentPairs_append_cons] at edge
      rw [show (stemHead :: stemTail) ++ new.toList ++ suffix =
        (stemHead :: stemTail) ++
          new.head :: (new.tail ++ suffix) by
            simp [Word.toList, List.append_assoc],
        listAdjacentPairs_append_cons]
      rcases List.mem_append.mp edge with stemEdge | boundaryOrRight
      · exact List.mem_append.mpr (Or.inl stemEdge)
      · apply List.mem_append.mpr
        right
        simp only [List.mem_cons] at boundaryOrRight ⊢
        rcases boundaryOrRight with boundary | rightEdge
        · left
          simpa [sameHead] using boundary
        · right
          exact
            replaceWord_rightContext_edgeMono sameFinal edgeMono
              suffix left right rightEdge

private theorem middleExpansion_core_edgeMono (u v : Word Nat) :
    ∀ left right,
      (left, right) ∈ (((u ++ v) ++ u).adjacentPairs) ->
        (left, right) ∈
          ((((u ++ v) ++ v) ++ u).adjacentPairs) := by
  intro left right edge
  rw [Word.adjacentPairs_append] at edge ⊢
  rcases List.mem_append.mp edge with first | boundaryOrU
  · apply List.mem_append.mpr
    left
    rw [Word.adjacentPairs_append]
    exact List.mem_append.mpr (Or.inl first)
  · apply List.mem_append.mpr
    right
    simpa [Word.final_append] using boundaryOrU

private theorem getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction head

private theorem word_toList_getLastD
    (word : Word Nat) (fallback : Nat) :
    word.toList.getLastD fallback = word.final := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [Word.toList, Word.final, List.getLastD_cons]

private theorem replaceWord_contextHead
    {old new source target : Word Nat} {stem suffix : List Nat}
    (sourceShape :
      source.toList = stem ++ old.toList ++ suffix)
    (targetShape :
      target.toList = stem ++ new.toList ++ suffix)
    (sameHead : new.head = old.head) :
    target.head = source.head := by
  cases stem with
  | nil =>
      have sourceHead : some source.head = some old.head := by
        simpa [Word.toList] using congrArg List.head? sourceShape
      have targetHead : some target.head = some new.head := by
        simpa [Word.toList] using congrArg List.head? targetShape
      exact Option.some.inj <|
        targetHead.trans <|
          (congrArg some sameHead).trans sourceHead.symm
  | cons stemHead stemTail =>
      have sourceHead : some source.head = some stemHead := by
        simpa [Word.toList] using congrArg List.head? sourceShape
      have targetHead : some target.head = some stemHead := by
        simpa [Word.toList] using congrArg List.head? targetShape
      exact Option.some.inj (targetHead.trans sourceHead.symm)

private theorem replaceWord_contextFinal
    {old new source target : Word Nat} {stem suffix : List Nat}
    (sourceShape :
      source.toList = stem ++ old.toList ++ suffix)
    (targetShape :
      target.toList = stem ++ new.toList ++ suffix)
    (sameFinal : new.final = old.final) :
    target.final = source.final := by
  have sourceFinal :
      source.final =
        (stem ++ old.toList ++ suffix).getLastD 0 := by
    calc
      source.final = source.toList.getLastD 0 :=
        (word_toList_getLastD source 0).symm
      _ = (stem ++ old.toList ++ suffix).getLastD 0 :=
        congrArg (fun letters => letters.getLastD 0) sourceShape
  have targetFinal :
      target.final =
        (stem ++ new.toList ++ suffix).getLastD 0 := by
    calc
      target.final = target.toList.getLastD 0 :=
        (word_toList_getLastD target 0).symm
      _ = (stem ++ new.toList ++ suffix).getLastD 0 :=
        congrArg (fun letters => letters.getLastD 0) targetShape
  have contextFinal :
      (stem ++ new.toList ++ suffix).getLastD 0 =
        (stem ++ old.toList ++ suffix).getLastD 0 := by
    cases suffix with
    | nil =>
        simp only [List.append_nil]
        rw [getLastD_append, getLastD_append,
          word_toList_getLastD, word_toList_getLastD, sameFinal]
    | cons suffixHead suffixTail =>
        simp only [getLastD_append, List.getLastD_cons]
  exact targetFinal.trans (contextFinal.trans sourceFinal.symm)

private theorem replaceWord_contextSupport
    {old new source target : Word Nat} {stem suffix : List Nat}
    (sourceShape :
      source.toList = stem ++ old.toList ++ suffix)
    (targetShape :
      target.toList = stem ++ new.toList ++ suffix)
    (sameSupport :
      ∀ letter, letter ∈ new.toList ↔ letter ∈ old.toList) :
    ∀ letter, letter ∈ target.toList ↔ letter ∈ source.toList := by
  intro letter
  rw [sourceShape, targetShape]
  simp only [List.mem_append]
  exact
    or_congr (or_congr Iff.rfl (sameSupport letter)) Iff.rfl

private theorem middleExpansion_contextExtension
    (source target u v : Word Nat) (stem suffix : List Nat)
    (sourceShape :
      source.toList =
        stem ++ (((u ++ v) ++ u).toList) ++ suffix)
    (targetShape :
      target.toList =
        stem ++ ((((u ++ v) ++ v) ++ u).toList) ++ suffix) :
    BoundarySupportEdgeExtension source target := by
  let old := (u ++ v) ++ u
  let new := ((u ++ v) ++ v) ++ u
  have coreHead : new.head = old.head := by
    simp [old, new]
  have coreFinal : new.final = old.final := by
    simp [old, new, Word.final_append]
  have coreSupport :
      ∀ letter, letter ∈ new.toList ↔ letter ∈ old.toList := by
    intro letter
    simp [old, new, Word.toList_append, or_assoc, or_left_comm,
      or_comm]
  have coreEdgeMono :
      ∀ left right,
        (left, right) ∈ old.adjacentPairs ->
          (left, right) ∈ new.adjacentPairs := by
    simpa [old, new] using middleExpansion_core_edgeMono u v
  refine
    { sameHead :=
        replaceWord_contextHead sourceShape targetShape coreHead
      sameFinal :=
        replaceWord_contextFinal sourceShape targetShape coreFinal
      sameSupport :=
        replaceWord_contextSupport sourceShape targetShape coreSupport
      edgeMono := ?_ }
  intro left right edge
  have listed :
      (left, right) ∈
        SemigroupBasis.CoRoots.S5_107.listAdjacentPairs
          (stem ++ old.toList ++ suffix) := by
    rw [← sourceShape, listAdjacentPairs_word]
    exact edge
  have replaced :=
    replaceWord_edgeMono coreHead coreFinal coreEdgeMono
      stem suffix left right listed
  rw [← targetShape, listAdjacentPairs_word] at replaced
  exact replaced

/-- The graph-only certificate needed to manufacture one chosen edge.
The core `u v u` uses only old vertices and edges, while the duplicated
middle walk `v` closes from `source` back to `target`. -/
structure MiddleEdgeWitness
    (ambient : Word Nat) (source target : Nat) where
  u : Word Nat
  v : Word Nat
  coreIn :
    SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient
      ((u ++ v) ++ u)
  vHead : v.head = target
  vFinal : v.final = source

private theorem directedPathIn_trans
    {ambient middle path : Word Nat}
    (middleIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient middle)
    (pathIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn middle path) :
    SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient path := by
  constructor
  · intro letter member
    exact middleIn.1 letter (pathIn.1 letter member)
  · intro source target edge
    exact middleIn.2 source target (pathIn.2 source target edge)

private theorem pathTail_nonempty_of_distinctEndpoints
    {path : Word Nat} {source target : Nat}
    (pathHead : path.head = source)
    (pathFinal : path.final = target)
    (different : source ≠ target) :
    path.tail ≠ [] := by
  intro empty
  have finalHead : path.final = path.head := by
    cases path with
    | mk head tail =>
        change tail = [] at empty
        subst tail
        rfl
  exact different (pathHead.symm.trans (finalHead.symm.trans pathFinal))

private theorem existsMiddleWord_of_path_missingEndpointEdge
    {ambient path : Word Nat} {source target : Nat}
    (pathIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient path)
    (pathHead : path.head = source)
    (pathFinal : path.final = target)
    (pathTailNonempty : path.tail ≠ [])
    (missing : (source, target) ∉ ambient.adjacentPairs) :
    ∃ middle : Word Nat,
      path.toList = source :: middle.toList ++ [target] := by
  cases path with
  | mk head tail =>
      cases tail with
      | nil =>
          exact False.elim (pathTailNonempty rfl)
      | cons next rest =>
          cases rest with
          | nil =>
              have pathEdge :
                  (head, next) ∈
                    (Word.mk head [next]).adjacentPairs := by
                simp [Word.adjacentPairs, Word.adjacentPairsFrom]
              have ambientEdge : (source, target) ∈ ambient.adjacentPairs := by
                have transported :=
                  pathIn.2 head next pathEdge
                have nextEq : next = target := by
                  simpa [Word.final] using pathFinal
                have headEq : head = source := pathHead
                simpa only [headEq, nextEq] using transported
              exact False.elim (missing ambientEdge)
          | cons after remaining =>
              let interior := (next :: after :: remaining).dropLast
              have interiorNonempty : interior ≠ [] := by
                simp [interior]
              let middle :=
                SemigroupBasis.CoRoots.S5_868.maximalFactorWord interior
              refine ⟨middle, ?_⟩
              rw [
                SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList
                  interiorNonempty]
              have reconstruction :=
                List.dropLast_concat_getLast
                  (l := next :: after :: remaining) (by simp)
              rw [List.getLast_eq_getLastD] at reconstruction
              rw [← pathHead, ← pathFinal]
              simpa [interior, Word.toList, Word.final] using
                reconstruction.symm

private theorem endpointEdges_of_middlePathShape
    {ambient path middle : Word Nat} {source target : Nat}
    (pathIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient path)
    (shape :
      path.toList = source :: middle.toList ++ [target]) :
    (source, middle.head) ∈ ambient.adjacentPairs ∧
      (middle.final, target) ∈ ambient.adjacentPairs := by
  have pathEq :
      path =
        (Word.singleton source ++ middle) ++ Word.singleton target := by
    apply Word.toList_injective
    simpa [Word.toList, List.append_assoc] using shape
  constructor
  · apply pathIn.2 source middle.head
    rw [pathEq, Word.adjacentPairs_append]
    apply List.mem_append.mpr
    left
    rw [Word.adjacentPairs_append]
    apply List.mem_append.mpr
    right
    change
      (source, middle.head) ∈
        (source, middle.head) :: middle.adjacentPairs
    exact List.Mem.head _
  · apply pathIn.2 middle.final target
    rw [pathEq, Word.adjacentPairs_append]
    apply List.mem_append.mpr
    right
    simpa only [Word.final_append] using
      (List.Mem.head (Word.singleton target).adjacentPairs :
        (middle.final, target) ∈
          (middle.final, target) ::
            (Word.singleton target).adjacentPairs)

private theorem middleCore_directedPathIn
    {ambient u v : Word Nat}
    (uIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient u)
    (vIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient v)
    (uToV : (u.final, v.head) ∈ ambient.adjacentPairs)
    (vToU : (v.final, u.head) ∈ ambient.adjacentPairs) :
    SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient
      ((u ++ v) ++ u) := by
  constructor
  · intro letter member
    simp only [Word.toList_append, List.mem_append] at member
    rcases member with (inU | inV) | inU
    · exact uIn.1 letter inU
    · exact vIn.1 letter inV
    · exact uIn.1 letter inU
  · intro source target edge
    rw [Word.adjacentPairs_append] at edge
    rcases List.mem_append.mp edge with first | finalPart
    · rw [Word.adjacentPairs_append] at first
      rcases List.mem_append.mp first with inU | boundaryOrV
      · exact uIn.2 source target inU
      · simp only [List.mem_cons] at boundaryOrV
        rcases boundaryOrV with boundary | inV
        · simp only [Prod.mk.injEq] at boundary
          rcases boundary with ⟨sourceEq, targetEq⟩
          subst source
          subst target
          simpa only [Word.final_append] using uToV
        · exact vIn.2 source target inV
    · simp only [List.mem_cons] at finalPart
      rcases finalPart with boundary | inU
      · simp only [Prod.mk.injEq] at boundary
        rcases boundary with ⟨sourceEq, targetEq⟩
        subst source
        subst target
        simpa only [Word.final_append] using vToU
      · exact uIn.2 source target inU

/-- A middle-edge witness produces a monotone marked-edge extension
containing the requested edge. -/
theorem derivesEdgeExtension_of_middleEdgeWitness
    (ambient : Word Nat)
    (indecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable ambient)
    {source target : Nat}
    (witness : MiddleEdgeWitness ambient source target) :
    ∃ expanded : Word Nat,
      Derives basis ambient expanded ∧
        BoundarySupportEdgeExtension ambient expanded ∧
        (source, target) ∈ expanded.adjacentPairs := by
  rcases existsSameMarkedDigraphWithFactor ambient
      ((witness.u ++ witness.v) ++ witness.u)
      indecomposable witness.coreIn with
    ⟨exposed, sameGraph, occurrence⟩
  rcases occurrence with ⟨stem, suffix, exposedShape⟩
  rcases derivesMiddleExpansionAtFactor exposed witness.u witness.v
      stem suffix exposedShape with
    ⟨expanded, expansion, expandedShape⟩
  have coreEdge :
      (witness.v.final, witness.v.head) ∈
        ((((witness.u ++ witness.v) ++ witness.v) ++
          witness.u).adjacentPairs) :=
    middleExpansion_addsClosingEdge witness.u witness.v
  have coreOccurs :
      SemigroupBasis.CoRoots.S5_868.OccursAsFactor
        (((witness.u ++ witness.v) ++ witness.v) ++ witness.u)
        expanded :=
    ⟨stem, suffix, expandedShape⟩
  have expandedEdge :
      (witness.v.final, witness.v.head) ∈ expanded.adjacentPairs :=
    SemigroupBasis.CoRoots.S5_868.occursAsFactor_edge
      coreOccurs witness.v.final witness.v.head coreEdge
  have ambientExposed :
      BoundarySupportEdgeExtension ambient exposed :=
    { sameHead := sameGraph.initial.symm
      sameFinal := sameGraph.final.symm
      sameSupport := fun letter => (sameGraph.support letter).symm
      edgeMono := fun left right edge =>
        (sameGraph.edge left right).mp edge }
  have exposedExpanded :
      BoundarySupportEdgeExtension exposed expanded :=
    middleExpansion_contextExtension exposed expanded witness.u witness.v
      stem suffix exposedShape expandedShape
  refine
    ⟨expanded,
      (derivesOfSameMarkedDigraph sameGraph).trans expansion,
      ambientExposed.trans exposedExpanded, ?_⟩
  simpa [witness.vFinal, witness.vHead] using expandedEdge

/-- Compatibility wrapper retaining the earlier one-edge API. -/
theorem derivesWordContainingEdge_of_middleEdgeWitness
    (ambient : Word Nat)
    (indecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable ambient)
    {source target : Nat}
    (witness : MiddleEdgeWitness ambient source target) :
    ∃ expanded : Word Nat,
      Derives basis ambient expanded ∧
        (source, target) ∈ expanded.adjacentPairs := by
  rcases derivesEdgeExtension_of_middleEdgeWitness
      ambient indecomposable witness with
    ⟨expanded, derivation, _, edge⟩
  exact ⟨expanded, derivation, edge⟩

/-- Exact residual graph lemma for the non-unary saturation route.  Unlike
`DerivationalCompleteness`, this statement is independent of equational
logic and can be falsified by a finite strongly connected directed graph.
The excluded unary case is handled separately by the repeated-unary
coordinate of the connected-cut signature. -/
def NonUnaryMiddleEdgeWitnessExistence : Prop :=
  ∀ (ambient : Word Nat) (source target other : Nat),
    SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable ambient ->
      source ∈ ambient.toList ->
        target ∈ ambient.toList ->
          other ∈ ambient.toList ->
            other ≠ source ->
              (source, target) ∉ ambient.adjacentPairs ->
                Nonempty (MiddleEdgeWitness ambient source target)

/-- Strong connectivity constructs the exact middle-edge witness.  The
loop case first takes a detour through the supplied distinct supported
vertex, ensuring that endpoint stripping leaves a nonempty middle word. -/
theorem nonUnaryMiddleEdgeWitnessExistence :
    NonUnaryMiddleEdgeWitnessExistence := by
  intro ambient source target other indecomposable sourceMember
    targetMember otherMember otherDifferent missing
  have backwardReachable :=
    indecomposable target targetMember source sourceMember
  rcases backwardReachable with
    ⟨backward, backwardHead, backwardFinal, backwardIn⟩
  have forwardData :
      ∃ forward : Word Nat,
        forward.head = source ∧
          forward.final = target ∧
          SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient forward ∧
          forward.tail ≠ [] := by
    by_cases different : source ≠ target
    · rcases indecomposable source sourceMember target targetMember with
        ⟨forward, forwardHead, forwardFinal, forwardIn⟩
      exact
        ⟨forward, forwardHead, forwardFinal, forwardIn,
          pathTail_nonempty_of_distinctEndpoints
            forwardHead forwardFinal different⟩
    · have sameEndpoint : source = target :=
        Classical.byContradiction different
      rcases indecomposable source sourceMember other otherMember with
        ⟨outward, outwardHead, outwardFinal, outwardIn⟩
      rcases indecomposable other otherMember source sourceMember with
        ⟨returning, returningHead, returningFinal, returningIn⟩
      have boundary : outward.final = returning.head :=
        outwardFinal.trans returningHead.symm
      let forward :=
        SemigroupBasis.CoRoots.S5_868.completionJoin outward returning
      have forwardIn :
          SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient forward :=
        SemigroupBasis.CoRoots.S5_868.completionJoin_directedPathIn
          boundary outwardIn returningIn
      have outwardTailNonempty : outward.tail ≠ [] :=
        pathTail_nonempty_of_distinctEndpoints outwardHead outwardFinal
          (Ne.symm otherDifferent)
      have forwardTailNonempty : forward.tail ≠ [] := by
        intro empty
        apply outwardTailNonempty
        have appended : outward.tail ++ returning.tail = [] := by
          simpa [forward,
            SemigroupBasis.CoRoots.S5_868.completionJoin] using empty
        exact (List.append_eq_nil_iff.mp appended).1
      have joinedFinal : forward.final = source := by
        exact
          (SemigroupBasis.CoRoots.S5_868.completionJoin_final
            boundary).trans returningFinal
      exact
        ⟨forward,
          (SemigroupBasis.CoRoots.S5_868.completionJoin_head
            outward returning).trans outwardHead,
          joinedFinal.trans sameEndpoint,
          forwardIn, forwardTailNonempty⟩
  rcases forwardData with
    ⟨forward, forwardHead, forwardFinal, forwardIn,
      forwardTailNonempty⟩
  rcases existsMiddleWord_of_path_missingEndpointEdge forwardIn
      forwardHead forwardFinal forwardTailNonempty missing with
    ⟨middle, middleShape⟩
  have middleOccurs :
      SemigroupBasis.CoRoots.S5_868.OccursAsFactor middle forward := by
    refine ⟨[source], [target], ?_⟩
    simpa using middleShape
  have middleInForward :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn forward middle :=
    SemigroupBasis.CoRoots.S5_868.directedPathIn_of_occursAsFactor
      middleOccurs
  have middleIn :
      SemigroupBasis.CoRoots.S5_868.DirectedPathIn ambient middle :=
    directedPathIn_trans forwardIn middleInForward
  have boundaries :=
    endpointEdges_of_middlePathShape forwardIn middleShape
  exact
    ⟨{ u := middle
       v := backward
       coreIn :=
         middleCore_directedPathIn middleIn backwardIn
           (by simpa [backwardHead] using boundaries.2)
           (by simpa [backwardFinal] using boundaries.1)
       vHead := backwardHead
       vFinal := backwardFinal }⟩

private def NonUnarySupport (word : Word Nat) : Prop :=
  ∃ left, left ∈ word.toList ∧
    ∃ right, right ∈ word.toList ∧ left ≠ right

private theorem nonUnarySupport_of_extension
    {source target : Word Nat}
    (extension : BoundarySupportEdgeExtension source target)
    (nonUnary : NonUnarySupport source) :
    NonUnarySupport target := by
  rcases nonUnary with
    ⟨left, leftMember, right, rightMember, different⟩
  exact
    ⟨left, (extension.sameSupport left).mpr leftMember,
      right, (extension.sameSupport right).mpr rightMember,
      different⟩

private theorem indecomposable_of_extension
    {source target : Word Nat}
    (extension : BoundarySupportEdgeExtension source target)
    (indecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable source) :
    SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable target := by
  intro left leftMember right rightMember
  have leftSource : left ∈ source.toList :=
    (extension.sameSupport left).mp leftMember
  have rightSource : right ∈ source.toList :=
    (extension.sameSupport right).mp rightMember
  rcases indecomposable left leftSource right rightSource with
    ⟨path, pathHead, pathFinal, pathIn⟩
  refine ⟨path, pathHead, pathFinal, ?_⟩
  constructor
  · intro letter member
    exact (extension.sameSupport letter).mpr
      (pathIn.1 letter member)
  · intro edgeLeft edgeRight edge
    exact extension.edgeMono edgeLeft edgeRight
      (pathIn.2 edgeLeft edgeRight edge)

private theorem derivesSingleEdgeExtension
    (source : Word Nat)
    (indecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable source)
    (nonUnary : NonUnarySupport source)
    (left right : Nat)
    (leftMember : left ∈ source.toList)
    (rightMember : right ∈ source.toList) :
    ∃ target : Word Nat,
      Derives basis source target ∧
        BoundarySupportEdgeExtension source target ∧
        (left, right) ∈ target.adjacentPairs := by
  by_cases present : (left, right) ∈ source.adjacentPairs
  · exact
      ⟨source, Derives.refl _,
        BoundarySupportEdgeExtension.refl source, present⟩
  · rcases nonUnary with
      ⟨first, firstMember, second, secondMember, firstDifferentSecond⟩
    have other :
        ∃ candidate, candidate ∈ source.toList ∧ candidate ≠ left := by
      by_cases leftFirst : left = first
      · exact
          ⟨second, secondMember, by
            intro secondLeft
            exact firstDifferentSecond
              (leftFirst.symm.trans secondLeft.symm)⟩
      · exact ⟨first, firstMember, Ne.symm leftFirst⟩
    rcases other with ⟨candidate, candidateMember, candidateDifferent⟩
    rcases
        nonUnaryMiddleEdgeWitnessExistence source left right candidate
          indecomposable leftMember rightMember candidateMember
          candidateDifferent present with
      ⟨witness⟩
    exact
      derivesEdgeExtension_of_middleEdgeWitness
        source indecomposable witness

private structure SaturationRun
    (source : Word Nat) (pairs : List (Nat × Nat)) where
  current : Word Nat
  derivation : Derives basis source current
  extension : BoundarySupportEdgeExtension source current
  covered :
    ∀ pair, pair ∈ pairs ->
      pair ∈ current.adjacentPairs

private theorem saturatePairList :
    ∀ (source : Word Nat) (pairs : List (Nat × Nat)),
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable source ->
        NonUnarySupport source ->
          (∀ pair, pair ∈ pairs ->
            pair.1 ∈ source.toList ∧ pair.2 ∈ source.toList) ->
            Nonempty (SaturationRun source pairs)
  | source, [], _, _, _ => by
      exact
        ⟨{ current := source
           derivation := Derives.refl _
           extension := BoundarySupportEdgeExtension.refl source
           covered := by simp }⟩
  | source, pair :: rest, indecomposable, nonUnary, supported => by
      have pairSupported := supported pair (by simp)
      rcases derivesSingleEdgeExtension source indecomposable nonUnary
          pair.1 pair.2 pairSupported.1 pairSupported.2 with
        ⟨next, firstDerivation, firstExtension, pairEdge⟩
      have nextIndecomposable :
          SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable next :=
        indecomposable_of_extension firstExtension indecomposable
      have nextNonUnary : NonUnarySupport next :=
        nonUnarySupport_of_extension firstExtension nonUnary
      have restSupported :
          ∀ candidate, candidate ∈ rest ->
            candidate.1 ∈ next.toList ∧
              candidate.2 ∈ next.toList := by
        intro candidate member
        have inSource :=
          supported candidate (List.Mem.tail pair member)
        exact
          ⟨(firstExtension.sameSupport candidate.1).mpr inSource.1,
            (firstExtension.sameSupport candidate.2).mpr inSource.2⟩
      rcases saturatePairList next rest nextIndecomposable
          nextNonUnary restSupported with
        ⟨remaining⟩
      refine
        ⟨{ current := remaining.current
           derivation := firstDerivation.trans remaining.derivation
           extension := firstExtension.trans remaining.extension
           covered := ?_ }⟩
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with equal | inRest
      · subst candidate
        exact remaining.extension.edgeMono pair.1 pair.2 pairEdge
      · exact remaining.covered candidate inRest

/-!
## Exact saturation residual

The witness theorem above removes all path-existence mathematics.  What
remains is the well-founded fold over the finite support-edge list.  Its
result type records every invariant needed by the final marked-digraph
comparison, so a proof cannot silently lose an earlier inserted edge.
-/

structure CompleteSupportSaturation (source : Word Nat) where
  saturated : Word Nat
  derivation : Derives basis source saturated
  sameHead : saturated.head = source.head
  sameFinal : saturated.final = source.final
  sameSupport :
    ∀ letter, letter ∈ saturated.toList ↔ letter ∈ source.toList
  completeEdges :
    ∀ left, left ∈ source.toList ->
      ∀ right, right ∈ source.toList ->
        (left, right) ∈ saturated.adjacentPairs

/-- Minimal remaining component-normalization theorem.  It is a finite
support fold, not a bounded-variable enumeration: every missing pair is
inserted by `nonUnaryMiddleEdgeWitnessExistence` followed by
`derivesWordContainingEdge_of_middleEdgeWitness`. -/
def NonUnaryCompleteSupportSaturation : Prop :=
  ∀ (source : Word Nat),
    SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable source ->
      (∃ left, left ∈ source.toList ∧
        ∃ right, right ∈ source.toList ∧ left ≠ right) ->
        Nonempty (CompleteSupportSaturation source)

/-- Unconditional finite missing-edge saturation of every non-unary
indecomposable word. -/
theorem nonUnaryCompleteSupportSaturation :
    NonUnaryCompleteSupportSaturation := by
  intro source indecomposable nonUnary
  let pairs :=
    source.toList.flatMap fun left =>
      source.toList.map fun right => (left, right)
  have supported :
      ∀ pair, pair ∈ pairs ->
        pair.1 ∈ source.toList ∧ pair.2 ∈ source.toList := by
    intro pair member
    simp only [pairs, List.mem_flatMap, List.mem_map] at member
    rcases member with
      ⟨left, leftMember, right, rightMember, rfl⟩
    exact ⟨leftMember, rightMember⟩
  rcases saturatePairList source pairs indecomposable nonUnary
      supported with
    ⟨run⟩
  exact
    ⟨{ saturated := run.current
       derivation := run.derivation
       sameHead := run.extension.sameHead
       sameFinal := run.extension.sameFinal
       sameSupport := run.extension.sameSupport
       completeEdges := by
         intro left leftMember right rightMember
         apply run.covered (left, right)
         simp [pairs, leftMember, rightMember] }⟩

/-!
## Bidirectional component comparison

The direct connected-cut signature records each maximal component's support,
unary-repeat state, and final letter.  Applying the same signature to the
reversed word records the corresponding initial letter.  The lemmas below
make that correspondence explicit and compare components after saturating
only the non-unary ones.
-/

private theorem disjoint_flatten_of_pairwise
    {first : List Nat} {rest : List (List Nat)}
    (pairwise :
      (first :: rest).Pairwise
        SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint) :
    SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint
      first rest.flatten := by
  intro letter firstMember flattenedMember
  rcases List.mem_flatten.mp flattenedMember with
    ⟨component, componentMember, letterMember⟩
  exact
    (List.pairwise_cons.mp pairwise).1 component componentMember
      letter firstMember letterMember

private theorem list_append_left_cancel
    (initial left right : List Nat)
    (equal : initial ++ left = initial ++ right) :
    left = right := by
  induction initial with
  | nil => simpa using equal
  | cons head tail induction =>
      exact induction (List.cons.inj equal).2

private theorem componentDecompositions_unique :
    ∀ (left right : List (List Nat)),
      left.flatten = right.flatten ->
        (∀ component, component ∈ left -> component ≠ []) ->
          (∀ component, component ∈ right -> component ≠ []) ->
            left.Pairwise
              SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint ->
              right.Pairwise
                SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint ->
                (∀ component, component ∈ left ->
                  SemigroupBasis.Examples.ConnectedComponentSupportConnected
                    component) ->
                  (∀ component, component ∈ right ->
                    SemigroupBasis.Examples.ConnectedComponentSupportConnected
                      component) ->
                    left = right
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], first :: rest, flattened, _, rightNonempty, _, _, _, _ => by
      have firstEmpty : first = [] := by
        have : first ++ rest.flatten = [] := by
          simpa using flattened.symm
        exact (List.append_eq_nil_iff.mp this).1
      exact False.elim (rightNonempty first (by simp) firstEmpty)
  | first :: rest, [], flattened, leftNonempty, _, _, _, _, _ => by
      have firstEmpty : first = [] := by
        have : first ++ rest.flatten = [] := by
          simpa using flattened
        exact (List.append_eq_nil_iff.mp this).1
      exact False.elim (leftNonempty first (by simp) firstEmpty)
  | leftFirst :: leftRest, rightFirst :: rightRest, flattened,
      leftNonempty, rightNonempty, leftPairwise, rightPairwise,
      leftConnected, rightConnected => by
      have leftFirstNonempty : leftFirst ≠ [] :=
        leftNonempty leftFirst (by simp)
      have rightFirstNonempty : rightFirst ≠ [] :=
        rightNonempty rightFirst (by simp)
      have leftFirstTailDisjoint :=
        disjoint_flatten_of_pairwise leftPairwise
      have rightFirstTailDisjoint :=
        disjoint_flatten_of_pairwise rightPairwise
      have firstEquality : leftFirst = rightFirst := by
        simp only [List.flatten_cons] at flattened
        rcases List.append_eq_append_iff.mp flattened with
          leftShorter | rightShorter
        · rcases leftShorter with
            ⟨extra, rightShape, tailShape⟩
          by_cases extraEmpty : extra = []
          · simpa [extraEmpty] using rightShape.symm
          · have connected :=
              rightConnected rightFirst (by simp)
            have intersection :=
              connected leftFirst extra rightShape
                leftFirstNonempty extraEmpty
            rcases intersection with
              ⟨letter, leftMember, extraMember⟩
            have tailMember : letter ∈ leftRest.flatten := by
              rw [tailShape]
              exact List.mem_append_left _ extraMember
            exact False.elim
              (leftFirstTailDisjoint letter leftMember tailMember)
        · rcases rightShorter with
            ⟨extra, leftShape, tailShape⟩
          by_cases extraEmpty : extra = []
          · simpa [extraEmpty] using leftShape
          · have connected :=
              leftConnected leftFirst (by simp)
            have intersection :=
              connected rightFirst extra leftShape
                rightFirstNonempty extraEmpty
            rcases intersection with
              ⟨letter, rightMember, extraMember⟩
            have tailMember : letter ∈ rightRest.flatten := by
              rw [tailShape]
              exact List.mem_append_left _ extraMember
            exact False.elim
              (rightFirstTailDisjoint letter rightMember tailMember)
      subst rightFirst
      congr 1
      apply componentDecompositions_unique leftRest rightRest
      · have tails :
            leftFirst ++ leftRest.flatten =
              leftFirst ++ rightRest.flatten := by
          simpa using flattened
        exact
          list_append_left_cancel leftFirst leftRest.flatten
            rightRest.flatten tails
      · intro component member
        exact leftNonempty component
          (List.Mem.tail leftFirst member)
      · intro component member
        exact rightNonempty component
          (List.Mem.tail leftFirst member)
      · exact (List.pairwise_cons.mp leftPairwise).2
      · exact (List.pairwise_cons.mp rightPairwise).2
      · intro component member
        exact leftConnected component
          (List.Mem.tail leftFirst member)
      · intro component member
        exact rightConnected component
          (List.Mem.tail leftFirst member)

private theorem connectedComponentSupportsDisjoint_symm
    {left right : List Nat}
    (disjoint :
      SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint
        left right) :
    SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint
      right left := by
  intro letter rightMember leftMember
  exact disjoint letter leftMember rightMember

private theorem connectedComponentSupportsDisjoint_reverse
    {left right : List Nat}
    (disjoint :
      SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint
        left right) :
    SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint
      left.reverse right.reverse := by
  intro letter leftMember rightMember
  exact disjoint letter
    (by simpa using leftMember) (by simpa using rightMember)

private theorem connectedComponentDecomposeList_reverse
    (letters : List Nat) :
    SemigroupBasis.Examples.connectedComponentDecomposeList
        letters.reverse =
      (SemigroupBasis.Examples.connectedComponentDecomposeList letters).reverse.map
        List.reverse := by
  let components :=
    SemigroupBasis.Examples.connectedComponentDecomposeList letters
  let reversedComponents := components.reverse.map List.reverse
  have sourceSpec :=
    SemigroupBasis.Examples.connectedComponentDecomposeList_spec letters
  have targetSpec :=
    SemigroupBasis.Examples.connectedComponentDecomposeList_spec
      letters.reverse
  apply componentDecompositions_unique
      (SemigroupBasis.Examples.connectedComponentDecomposeList
        letters.reverse) reversedComponents
  · rw [targetSpec.flatten_eq]
    change letters.reverse = reversedComponents.flatten
    have reversedFlatten :
        reversedComponents.flatten = components.flatten.reverse := by
      simpa [reversedComponents] using
        (List.reverse_flatten (L := components)).symm
    calc
      letters.reverse = components.flatten.reverse :=
        (congrArg List.reverse sourceSpec.flatten_eq).symm
      _ = reversedComponents.flatten := reversedFlatten.symm
  · exact targetSpec.nonempty
  · intro component member
    change component ∈ components.reverse.map List.reverse at member
    rcases List.mem_map.mp member with
      ⟨original, originalMember, rfl⟩
    have inComponents : original ∈ components := by
      simpa using originalMember
    simpa using sourceSpec.nonempty original inComponents
  · exact targetSpec.pairwiseDisjoint
  · change
      (components.reverse.map List.reverse).Pairwise
        SemigroupBasis.Examples.ConnectedComponentSupportsDisjoint
    rw [List.pairwise_map, List.pairwise_reverse]
    exact sourceSpec.pairwiseDisjoint.imp fun disjoint =>
      connectedComponentSupportsDisjoint_reverse
        (connectedComponentSupportsDisjoint_symm disjoint)
  · exact targetSpec.supportConnected
  · intro component member
    change component ∈ components.reverse.map List.reverse at member
    rcases List.mem_map.mp member with
      ⟨original, originalMember, rfl⟩
    have inComponents : original ∈ components := by
      simpa using originalMember
    exact
      SemigroupBasis.CoRoots.S5_804.connectedComponentSupportConnected_reverse
        (sourceSpec.supportConnected original inComponents)

private abbrev componentSignature (letters : List Nat) :=
  SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList
    letters

private theorem componentFinal_eq_wordFinal
    {letters : List Nat} (nonempty : letters ≠ []) :
    SemigroupBasis.CoRoots.S5_804.componentFinal letters =
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).final := by
  rcases List.exists_cons_of_ne_nil nonempty with
    ⟨head, tail, rfl⟩
  rfl

private theorem componentFinal_append_singleton
    (initial : List Nat) (last : Nat) :
    SemigroupBasis.CoRoots.S5_804.componentFinal (initial ++ [last]) =
      last := by
  cases initial with
  | nil => rfl
  | cons head tail =>
      simp only [List.cons_append,
        SemigroupBasis.CoRoots.S5_804.componentFinal]
      rw [getLastD_append]
      rfl

private theorem componentFinal_reverse_eq_wordHead
    {letters : List Nat} (nonempty : letters ≠ []) :
    SemigroupBasis.CoRoots.S5_804.componentFinal letters.reverse =
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).head := by
  rcases List.exists_cons_of_ne_nil nonempty with
    ⟨head, tail, rfl⟩
  simpa [List.reverse_cons,
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord,
    SemigroupBasis.CoRoots.S5_868.completionWordOfList] using
      componentFinal_append_singleton tail.reverse head

private theorem componentSupport_iff_of_signature_eq
    {left right : List Nat}
    (same : componentSignature left = componentSignature right)
    (letter : Nat) :
    letter ∈ left ↔ letter ∈ right := by
  have baseEquality :=
    congrArg
      (fun signature => signature.base.support) same
  simp only [componentSignature,
    SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList,
    SemigroupBasis.Examples.connectedComponentSignatureOfList_support]
      at baseEquality
  calc
    letter ∈ left ↔
        letter ∈
          SemigroupBasis.Examples.connectedComponentSortedSupport left :=
      (SemigroupBasis.Examples.connectedComponentSortedSupport_mem_iff
        letter left).symm
    _ ↔
        letter ∈
          SemigroupBasis.Examples.connectedComponentSortedSupport right := by
      rw [baseEquality]
    _ ↔ letter ∈ right :=
      SemigroupBasis.Examples.connectedComponentSortedSupport_mem_iff
        letter right

private theorem componentFinal_eq_of_signature_eq
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (same : componentSignature left = componentSignature right) :
    (SemigroupBasis.CoRoots.S5_868.maximalFactorWord left).final =
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord right).final := by
  rw [← componentFinal_eq_wordFinal leftNonempty,
    ← componentFinal_eq_wordFinal rightNonempty]
  exact congrArg (fun signature => signature.final) same

private theorem componentHead_eq_of_reverse_signature_eq
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (same :
      componentSignature left.reverse =
        componentSignature right.reverse) :
    (SemigroupBasis.CoRoots.S5_868.maximalFactorWord left).head =
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord right).head := by
  rw [← componentFinal_reverse_eq_wordHead leftNonempty,
    ← componentFinal_reverse_eq_wordHead rightNonempty]
  exact congrArg (fun signature => signature.final) same

private theorem adjacentPair_support
    {word : Word Nat} {left right : Nat}
    (edge : (left, right) ∈ word.adjacentPairs) :
    left ∈ word.toList ∧ right ∈ word.toList := by
  rcases
      (SemigroupBasis.CoRoots.S5_107.mem_adjacentPairs_iff_exists_split
        left right word).mp edge with
    ⟨before, after, shape⟩
  rw [shape]
  simp

private theorem adjacentPair_toList_length_ne_one
    {word : Word Nat} {left right : Nat}
    (edge : (left, right) ∈ word.adjacentPairs) :
    word.toList.length ≠ 1 := by
  intro singletonLength
  rcases
      (SemigroupBasis.CoRoots.S5_107.mem_adjacentPairs_iff_exists_split
        left right word).mp edge with
    ⟨before, after, shape⟩
  have lengths := congrArg List.length shape
  rw [singletonLength] at lengths
  simp only [List.length_append, List.length_cons] at lengths
  omega

private theorem saturated_sameMarkedDigraph
    {leftSource rightSource : Word Nat}
    (sameHead : leftSource.head = rightSource.head)
    (sameFinal : leftSource.final = rightSource.final)
    (sameSupport :
      ∀ letter,
        letter ∈ leftSource.toList ↔ letter ∈ rightSource.toList)
    (left : CompleteSupportSaturation leftSource)
    (right : CompleteSupportSaturation rightSource) :
    left.saturated.SameMarkedDigraph right.saturated := by
  refine ⟨left.sameHead.trans (sameHead.trans right.sameHead.symm),
    left.sameFinal.trans (sameFinal.trans right.sameFinal.symm), ?_, ?_⟩
  · intro letter
    exact (left.sameSupport letter).trans <|
      (sameSupport letter).trans (right.sameSupport letter).symm
  · intro edgeLeft edgeRight
    constructor
    · intro edge
      have supported := adjacentPair_support edge
      apply right.completeEdges edgeLeft
      · exact (sameSupport edgeLeft).mp
          ((left.sameSupport edgeLeft).mp supported.1)
      · exact (sameSupport edgeRight).mp
          ((left.sameSupport edgeRight).mp supported.2)
    · intro edge
      have supported := adjacentPair_support edge
      apply left.completeEdges edgeLeft
      · exact (sameSupport edgeLeft).mpr
          ((right.sameSupport edgeLeft).mp supported.1)
      · exact (sameSupport edgeRight).mpr
          ((right.sameSupport edgeRight).mp supported.2)

private theorem unarySupport_of_not_nonUnary
    (word : Word Nat) (notNonUnary : ¬NonUnarySupport word) :
    ∀ letter, letter ∈ word.toList -> letter = word.head := by
  intro letter member
  by_cases equal : letter = word.head
  · exact equal
  · apply False.elim
    apply notNonUnary
    exact
      ⟨letter, member, word.head, by simp [Word.toList], equal⟩

private theorem nonUnarySupport_of_support_iff
    {left right : Word Nat}
    (sameSupport :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList)
    (nonUnary : NonUnarySupport left) :
    NonUnarySupport right := by
  rcases nonUnary with
    ⟨first, firstMember, second, secondMember, different⟩
  exact
    ⟨first, (sameSupport first).mp firstMember,
      second, (sameSupport second).mp secondMember, different⟩

private theorem componentSortedSupport_eq_singleton_of_unary
    {letters : List Nat} (nonempty : letters ≠ [])
    (unary :
      ∀ letter,
        letter ∈
            (SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).toList ->
          letter =
            (SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).head) :
    SemigroupBasis.Examples.connectedComponentSortedSupport letters =
      [(SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).head] := by
  let word :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters
  let support :=
    SemigroupBasis.Examples.connectedComponentSortedSupport letters
  have wordList : word.toList = letters :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList nonempty
  have supportNonempty : support ≠ [] := by
    exact
      SemigroupBasis.Examples.connectedComponentSortedSupport_nonempty
        nonempty
  cases supportShape : support with
  | nil => contradiction
  | cons first rest =>
      have firstInLetters : first ∈ letters := by
        rw [←
          SemigroupBasis.Examples.connectedComponentSortedSupport_mem_iff]
        simpa [support, supportShape]
      have firstEqual : first = word.head :=
        unary first (by
          rw [SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList
            nonempty]
          exact firstInLetters)
      cases rest with
      | nil =>
          simpa [support, supportShape, word, firstEqual]
      | cons second remaining =>
          have secondInLetters : second ∈ letters := by
            rw [←
              SemigroupBasis.Examples.connectedComponentSortedSupport_mem_iff]
            simp [support, supportShape]
          have secondEqual : second = word.head :=
            unary second (by
              rw [SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList
                nonempty]
              exact secondInLetters)
          have nodupSupport : support.Nodup := by
            simpa [support] using
              SemigroupBasis.Examples.connectedComponentSortedSupport_nodup
                letters
          rw [supportShape, firstEqual, secondEqual] at nodupSupport
          simp at nodupSupport

private theorem componentRepeatedUnary_eq_decide
    {letters : List Nat} (nonempty : letters ≠ [])
    (unary :
      ∀ letter,
        letter ∈
            (SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).toList ->
          letter =
            (SemigroupBasis.CoRoots.S5_868.maximalFactorWord letters).head) :
    (componentSignature letters).base.repeatedUnary =
      decide (letters.length ≠ 1) := by
  have singleton :=
    componentSortedSupport_eq_singleton_of_unary nonempty unary
  simp [componentSignature,
    SemigroupBasis.CoRoots.S5_804.connectedCutComponentSignatureOfList,
    SemigroupBasis.Examples.connectedComponentSignatureOfList,
    singleton]

private theorem unaryLoop_of_length_ne_one
    (word : Word Nat)
    (unary :
      ∀ letter, letter ∈ word.toList -> letter = word.head)
    (notOne : word.toList.length ≠ 1) :
    (word.head, word.head) ∈ word.adjacentPairs := by
  cases word with
  | mk head tail =>
      cases tail with
      | nil =>
          exact False.elim (notOne (by simp [Word.toList]))
      | cons second rest =>
          have secondEqual : second = head :=
            unary second (by simp [Word.toList])
          subst second
          change
            (head, head) ∈
              (head, head) :: Word.adjacentPairsFrom head rest
          exact List.Mem.head _

private theorem unary_sameMarkedDigraph_of_componentSignatures
    {leftLetters rightLetters : List Nat}
    (leftNonempty : leftLetters ≠ [])
    (rightNonempty : rightLetters ≠ [])
    (directSame :
      componentSignature leftLetters =
        componentSignature rightLetters)
    (reverseSame :
      componentSignature leftLetters.reverse =
        componentSignature rightLetters.reverse)
    (leftNotNonUnary :
      ¬NonUnarySupport
        (SemigroupBasis.CoRoots.S5_868.maximalFactorWord leftLetters)) :
    (SemigroupBasis.CoRoots.S5_868.maximalFactorWord leftLetters).SameMarkedDigraph
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord rightLetters) := by
  let left :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord leftLetters
  let right :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord rightLetters
  have leftList : left.toList = leftLetters :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList leftNonempty
  have rightList : right.toList = rightLetters :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList rightNonempty
  have sameSupport :
      ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList := by
    intro letter
    rw [leftList, rightList]
    exact componentSupport_iff_of_signature_eq directSame letter
  have sameHead : left.head = right.head :=
    componentHead_eq_of_reverse_signature_eq
      leftNonempty rightNonempty reverseSame
  have sameFinal : left.final = right.final :=
    componentFinal_eq_of_signature_eq
      leftNonempty rightNonempty directSame
  have leftUnary :
      ∀ letter, letter ∈ left.toList -> letter = left.head :=
    unarySupport_of_not_nonUnary left leftNotNonUnary
  have rightNotNonUnary : ¬NonUnarySupport right := by
    intro rightNonUnary
    apply leftNotNonUnary
    exact nonUnarySupport_of_support_iff
      (fun letter => (sameSupport letter).symm) rightNonUnary
  have rightUnary :
      ∀ letter, letter ∈ right.toList -> letter = right.head :=
    unarySupport_of_not_nonUnary right rightNotNonUnary
  have repeatedEqual :
      (componentSignature leftLetters).base.repeatedUnary =
        (componentSignature rightLetters).base.repeatedUnary :=
    congrArg (fun signature => signature.base.repeatedUnary) directSame
  have lengthStatus :
      left.toList.length ≠ 1 ↔ right.toList.length ≠ 1 := by
    have leftRepeated :=
      componentRepeatedUnary_eq_decide leftNonempty
        (by simpa [left] using leftUnary)
    have rightRepeated :=
      componentRepeatedUnary_eq_decide rightNonempty
        (by simpa [right] using rightUnary)
    constructor
    · intro leftLong
      have leftLettersLong : leftLetters.length ≠ 1 := by
        simpa [leftList] using leftLong
      have decided : decide (leftLetters.length ≠ 1) = true :=
        decide_eq_true leftLettersLong
      rw [← leftRepeated, repeatedEqual, rightRepeated] at decided
      have rightLettersLong : rightLetters.length ≠ 1 :=
        of_decide_eq_true decided
      simpa [rightList] using rightLettersLong
    · intro rightLong
      have rightLettersLong : rightLetters.length ≠ 1 := by
        simpa [rightList] using rightLong
      have decided : decide (rightLetters.length ≠ 1) = true :=
        decide_eq_true rightLettersLong
      rw [← rightRepeated, ← repeatedEqual, leftRepeated] at decided
      have leftLettersLong : leftLetters.length ≠ 1 :=
        of_decide_eq_true decided
      simpa [leftList] using leftLettersLong
  refine ⟨sameHead, sameFinal, sameSupport, ?_⟩
  intro edgeLeft edgeRight
  constructor
  · intro edge
    have supported := adjacentPair_support edge
    have edgeLeftEq := leftUnary edgeLeft supported.1
    have edgeRightEq := leftUnary edgeRight supported.2
    have leftLong : left.toList.length ≠ 1 :=
      adjacentPair_toList_length_ne_one edge
    have rightLoop :=
      unaryLoop_of_length_ne_one right rightUnary
        (lengthStatus.mp leftLong)
    simpa [edgeLeftEq, edgeRightEq, sameHead] using rightLoop
  · intro edge
    have supported := adjacentPair_support edge
    have edgeLeftEq := rightUnary edgeLeft supported.1
    have edgeRightEq := rightUnary edgeRight supported.2
    have rightLong : right.toList.length ≠ 1 :=
      adjacentPair_toList_length_ne_one edge
    have leftLoop :=
      unaryLoop_of_length_ne_one left leftUnary
        (lengthStatus.mpr rightLong)
    simpa [edgeLeftEq, edgeRightEq, sameHead] using leftLoop

private theorem derivesFactor_of_componentSignatures
    {leftLetters rightLetters : List Nat}
    (leftNonempty : leftLetters ≠ [])
    (rightNonempty : rightLetters ≠ [])
    (leftIndecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable
        (SemigroupBasis.CoRoots.S5_868.maximalFactorWord leftLetters))
    (rightIndecomposable :
      SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable
        (SemigroupBasis.CoRoots.S5_868.maximalFactorWord rightLetters))
    (directSame :
      componentSignature leftLetters =
        componentSignature rightLetters)
    (reverseSame :
      componentSignature leftLetters.reverse =
        componentSignature rightLetters.reverse) :
    Derives basis
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord leftLetters)
      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord rightLetters) := by
  let left :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord leftLetters
  let right :=
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord rightLetters
  by_cases leftNonUnary : NonUnarySupport left
  · have leftList : left.toList = leftLetters :=
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList leftNonempty
    have rightList : right.toList = rightLetters :=
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList rightNonempty
    have sameSupport :
        ∀ letter, letter ∈ left.toList ↔ letter ∈ right.toList := by
      intro letter
      rw [leftList, rightList]
      exact componentSupport_iff_of_signature_eq directSame letter
    have rightNonUnary :
        NonUnarySupport right :=
      nonUnarySupport_of_support_iff sameSupport leftNonUnary
    rcases nonUnaryCompleteSupportSaturation
        left leftIndecomposable leftNonUnary with
      ⟨leftSaturation⟩
    rcases nonUnaryCompleteSupportSaturation
        right rightIndecomposable rightNonUnary with
      ⟨rightSaturation⟩
    have sameHead : left.head = right.head :=
      componentHead_eq_of_reverse_signature_eq
        leftNonempty rightNonempty reverseSame
    have sameFinal : left.final = right.final :=
      componentFinal_eq_of_signature_eq
        leftNonempty rightNonempty directSame
    have saturatedGraph :=
      saturated_sameMarkedDigraph sameHead sameFinal sameSupport
        leftSaturation rightSaturation
    exact leftSaturation.derivation.trans <|
      (derivesOfSameMarkedDigraph saturatedGraph).trans
        rightSaturation.derivation.symm
  · exact derivesOfSameMarkedDigraph <|
      unary_sameMarkedDigraph_of_componentSignatures
        leftNonempty rightNonempty directSame reverseSame leftNonUnary

private theorem flatten_nonempty_of_components
    {components : List (List Nat)}
    (componentsNonempty : components ≠ [])
    (nonempty :
      ∀ component, component ∈ components -> component ≠ []) :
    components.flatten ≠ [] := by
  rcases List.exists_cons_of_ne_nil componentsNonempty with
    ⟨first, rest, rfl⟩
  have firstNonempty := nonempty first (by simp)
  simpa using
    List.append_ne_nil_of_left_ne_nil firstNonempty rest.flatten

private theorem maximalFactorWord_flatten_cons
    {first : List Nat} {rest : List (List Nat)}
    (firstNonempty : first ≠ [])
    (restNonempty : rest.flatten ≠ []) :
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord
        (first :: rest).flatten =
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord first ++
        SemigroupBasis.CoRoots.S5_868.maximalFactorWord rest.flatten := by
  have wholeNonempty : (first :: rest).flatten ≠ [] := by
    simpa only [List.flatten_cons] using
      List.append_ne_nil_of_left_ne_nil firstNonempty rest.flatten
  apply Word.toList_injective
  rw [Word.toList_append,
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList
      wholeNonempty,
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList firstNonempty,
    SemigroupBasis.CoRoots.S5_868.maximalFactorWord_toList restNonempty]
  rfl

private theorem derives_of_componentSignatureChains :
    ∀ (leftFactors rightFactors : List (List Nat)),
      (∀ component, component ∈ leftFactors -> component ≠ []) ->
        (∀ component, component ∈ rightFactors -> component ≠ []) ->
          (∀ component, component ∈ leftFactors ->
            SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable
              (SemigroupBasis.CoRoots.S5_868.maximalFactorWord component)) ->
            (∀ component, component ∈ rightFactors ->
              SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable
                (SemigroupBasis.CoRoots.S5_868.maximalFactorWord component)) ->
              leftFactors.map componentSignature =
                  rightFactors.map componentSignature ->
                leftFactors.map
                    (fun component => componentSignature component.reverse) =
                  rightFactors.map
                    (fun component => componentSignature component.reverse) ->
                  Derives basis
                    (SemigroupBasis.CoRoots.S5_868.maximalFactorWord
                      leftFactors.flatten)
                    (SemigroupBasis.CoRoots.S5_868.maximalFactorWord
                      rightFactors.flatten)
  | [], [], _, _, _, _, _, _ => Derives.refl _
  | [], rightFirst :: rightRest, _, _, _, _, directSame, _ => by
      simp at directSame
  | leftFirst :: leftRest, [], _, _, _, _, directSame, _ => by
      simp at directSame
  | leftFirst :: leftRest, rightFirst :: rightRest,
      leftNonempty, rightNonempty, leftIndecomposable,
      rightIndecomposable, directSame, reverseSame => by
      simp only [List.map_cons, List.cons.injEq] at directSame
      simp only [List.map_cons, List.cons.injEq] at reverseSame
      have headDerivation :=
        derivesFactor_of_componentSignatures
          (leftNonempty leftFirst (by simp))
          (rightNonempty rightFirst (by simp))
          (leftIndecomposable leftFirst (by simp))
          (rightIndecomposable rightFirst (by simp))
          directSame.1 reverseSame.1
      cases leftRest with
      | nil =>
          cases rightRest with
          | nil =>
              simpa using headDerivation
          | cons rightSecond rightTail =>
              simp at directSame
      | cons leftSecond leftTail =>
          cases rightRest with
          | nil =>
              simp at directSame
          | cons rightSecond rightTail =>
              let leftRemaining := leftSecond :: leftTail
              let rightRemaining := rightSecond :: rightTail
              have leftRemainingNonempty :
                  ∀ component, component ∈ leftRemaining ->
                    component ≠ [] := by
                intro component member
                exact leftNonempty component
                  (List.Mem.tail leftFirst member)
              have rightRemainingNonempty :
                  ∀ component, component ∈ rightRemaining ->
                    component ≠ [] := by
                intro component member
                exact rightNonempty component
                  (List.Mem.tail rightFirst member)
              have leftRemainingIndecomposable :
                  ∀ component, component ∈ leftRemaining ->
                    SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable
                      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord
                        component) := by
                intro component member
                exact leftIndecomposable component
                  (List.Mem.tail leftFirst member)
              have rightRemainingIndecomposable :
                  ∀ component, component ∈ rightRemaining ->
                    SemigroupBasis.CoRoots.S5_868.TrahtmanIndecomposable
                      (SemigroupBasis.CoRoots.S5_868.maximalFactorWord
                        component) := by
                intro component member
                exact rightIndecomposable component
                  (List.Mem.tail rightFirst member)
              have tailDerivation :=
                derives_of_componentSignatureChains
                  leftRemaining rightRemaining
                  leftRemainingNonempty rightRemainingNonempty
                  leftRemainingIndecomposable
                  rightRemainingIndecomposable
                  directSame.2 reverseSame.2
              have leftTailNonempty :
                  leftRemaining.flatten ≠ [] :=
                flatten_nonempty_of_components (by simp)
                  leftRemainingNonempty
              have rightTailNonempty :
                  rightRemaining.flatten ≠ [] :=
                flatten_nonempty_of_components (by simp)
                  rightRemainingNonempty
              have replaceHead :=
                Derives.appendRight headDerivation
                  (SemigroupBasis.CoRoots.S5_868.maximalFactorWord
                    leftRemaining.flatten)
              have replaceTail :=
                Derives.prepend
                  (SemigroupBasis.CoRoots.S5_868.maximalFactorWord
                    rightFirst)
                  tailDerivation
              rw [maximalFactorWord_flatten_cons
                    (leftNonempty leftFirst (by simp))
                    leftTailNonempty,
                  maximalFactorWord_flatten_cons
                    (rightNonempty rightFirst (by simp))
                    rightTailNonempty]
              exact replaceHead.trans replaceTail

/-!
## Unrestricted completeness

The component saturation and bidirectional endpoint comparison above supply
the shared unrestricted theorem for all three order-six tables.
-/

/-- The exact unrestricted Nat-level theorem required by all three roots. -/
def DerivationalCompleteness : Prop :=
  ∀ {left right : Word Nat},
    SameBidirectionalConnectedCutSignature left right ->
      Derives basis left right

theorem derivationalCompleteness : DerivationalCompleteness := by
  intro left right same
  let leftFactors :=
    SemigroupBasis.Examples.connectedComponentDecomposeWord left
  let rightFactors :=
    SemigroupBasis.Examples.connectedComponentDecomposeWord right
  have leftFactorization :
      SemigroupBasis.CoRoots.S5_868.MaximalIndecomposableFactorization
        left leftFactors := by
    exact
      SemigroupBasis.CoRoots.S5_868.connectedComponentDecomposeWord_maximalFactorization
        left
  have rightFactorization :
      SemigroupBasis.CoRoots.S5_868.MaximalIndecomposableFactorization
        right rightFactors := by
    exact
      SemigroupBasis.CoRoots.S5_868.connectedComponentDecomposeWord_maximalFactorization
        right
  have directSame :
      leftFactors.map componentSignature =
        rightFactors.map componentSignature := by
    simpa [leftFactors, rightFactors,
      SemigroupBasis.CoRoots.S5_804.SameConnectedCutSignature,
      SemigroupBasis.CoRoots.S5_804.connectedCutSignaturesWord,
      SemigroupBasis.CoRoots.S5_804.connectedCutSignaturesList] using same.1
  have reversedSignatures :
      (leftFactors.map
          (fun component => componentSignature component.reverse)).reverse =
        (rightFactors.map
          (fun component => componentSignature component.reverse)).reverse := by
    simpa [leftFactors, rightFactors,
      SemigroupBasis.CoRoots.S5_804.SameConnectedCutSignature,
      SemigroupBasis.CoRoots.S5_804.connectedCutSignaturesWord,
      SemigroupBasis.CoRoots.S5_804.connectedCutSignaturesList,
      SemigroupBasis.Examples.connectedComponentDecomposeWord,
      connectedComponentDecomposeList_reverse,
      List.map_reverse, List.map_map, Function.comp_def] using same.2
  have reverseSame :
      leftFactors.map
          (fun component => componentSignature component.reverse) =
        rightFactors.map
          (fun component => componentSignature component.reverse) := by
    have reversedAgain := congrArg List.reverse reversedSignatures
    simpa using reversedAgain
  have componentDerivation :=
    derives_of_componentSignatureChains leftFactors rightFactors
      leftFactorization.nonempty rightFactorization.nonempty
      leftFactorization.indecomposable rightFactorization.indecomposable
      directSame reverseSame
  have leftEq :
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord
          leftFactors.flatten =
        left := by
    exact
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord_eq_of_toList
        leftFactorization.flatten_eq.symm
  have rightEq :
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord
          rightFactors.flatten =
        right := by
    exact
      SemigroupBasis.CoRoots.S5_868.maximalFactorWord_eq_of_toList
        rightFactorization.flatten_eq.symm
  simpa [leftEq, rightEq] using componentDerivation

/-- Equivalent factor-theory formulation of the shared theorem.  This is
the completeness of the intersection of the identity theories of `S5_804`
and its opposite. -/
def DetectorIntersectionCompleteness : Prop :=
  ∀ identity : Identity Nat,
    identity.SatisfiedBy detectorTable.semigroup ->
      identity.SatisfiedBy detectorTable.semigroup.opposite ->
        Derives basis identity.lhs identity.rhs

/-- Equal bidirectional signatures imply validity in both detector factors.
This is the semantic half of the exact reduction to the detector
intersection. -/
theorem detectorValidity_of_sameBidirectionalConnectedCutSignature
    {left right : Word Nat}
    (same : SameBidirectionalConnectedCutSignature left right) :
    (Identity.mk left right).SatisfiedBy detectorTable.semigroup ∧
      (Identity.mk left right).SatisfiedBy
        detectorTable.semigroup.opposite := by
  have directValid :
      (Identity.mk left right).SatisfiedBy detectorTable.semigroup := by
    intro valuation
    exact
      (SemigroupBasis.CoRoots.S5_804.derivesOfSameConnectedCutSignature
        same.1).sound
          SemigroupBasis.CoRoots.S5_804.catalogueModels valuation
  have reversedValid :
      (Identity.mk left right).reversed.SatisfiedBy
        detectorTable.semigroup := by
    intro valuation
    exact
      (SemigroupBasis.CoRoots.S5_804.derivesOfSameConnectedCutSignature
        same.2).sound
          SemigroupBasis.CoRoots.S5_804.catalogueModels valuation
  exact
    ⟨directValid,
      (Identity.satisfiedBy_opposite_iff_reversed
        (Identity.mk left right) detectorTable.semigroup).mpr
          reversedValid⟩

/-- The two exact formulations of the sole unbounded proof obligation are
equivalent.  This theorem prevents later workers from reproving the semantic
detector reduction and leaves only the common equational theory to solve. -/
theorem derivationalCompleteness_iff_detectorIntersectionCompleteness :
    DerivationalCompleteness ↔ DetectorIntersectionCompleteness := by
  constructor
  · intro complete identity directValid oppositeValid
    exact complete <|
      sameBidirectionalConnectedCutSignature_of_detectorValidity
        identity directValid oppositeValid
  · intro complete left right same
    have valid :=
      detectorValidity_of_sameBidirectionalConnectedCutSignature same
    exact complete (Identity.mk left right) valid.1 valid.2

/-- Produce the requested direct derivation from the factor-intersection
formulation. -/
theorem
    derivesOfSameBidirectionalConnectedCutSignature_of_detectorIntersection
    (complete : DetectorIntersectionCompleteness)
    {left right : Word Nat}
    (same : SameBidirectionalConnectedCutSignature left right) :
    Derives basis left right :=
  derivationalCompleteness_iff_detectorIntersectionCompleteness.mpr
    complete same

/-!
## Representative and opposite endpoint closure

Once `DerivationalCompleteness` is proved, each representative endpoint and
its literal reversed-basis opposite are immediate.  Naming all six endpoints
here keeps the eventual proof insertion to one shared theorem.
-/

structure TargetBasisPair (table : FiniteTable) : Prop where
  representative : BasisFor table.semigroup basis
  opposite :
    BasisFor table.semigroup.opposite (reversedBasis basis)

theorem targetBasisPair_of_derivationalCompleteness
    (complete : DerivationalCompleteness)
    {table : FiniteTable} (evidence : TargetEvidence table) :
    TargetBasisPair table := by
  have representative :=
    basisFor_of_targetEvidence complete evidence
  exact
    ⟨representative, representative.oppositeReversed⟩

theorem S6_13403.basisPair_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    TargetBasisPair S6_13403.table :=
  targetBasisPair_of_derivationalCompleteness complete S6_13403.evidence

theorem S6_13403.representativeBasisFor_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor S6_13403.table.semigroup basis :=
  (S6_13403.basisPair_of_derivationalCompleteness complete).representative

theorem S6_13403.oppositeBasisFor_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor S6_13403.table.semigroup.opposite (reversedBasis basis) :=
  (S6_13403.basisPair_of_derivationalCompleteness complete).opposite

theorem S6_13408.basisPair_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    TargetBasisPair S6_13408.table :=
  targetBasisPair_of_derivationalCompleteness complete S6_13408.evidence

theorem S6_13408.representativeBasisFor_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor S6_13408.table.semigroup basis :=
  (S6_13408.basisPair_of_derivationalCompleteness complete).representative

theorem S6_13408.oppositeBasisFor_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor S6_13408.table.semigroup.opposite (reversedBasis basis) :=
  (S6_13408.basisPair_of_derivationalCompleteness complete).opposite

theorem S6_13409.basisPair_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    TargetBasisPair S6_13409.table :=
  targetBasisPair_of_derivationalCompleteness complete S6_13409.evidence

theorem S6_13409.representativeBasisFor_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor S6_13409.table.semigroup basis :=
  (S6_13409.basisPair_of_derivationalCompleteness complete).representative

theorem S6_13409.oppositeBasisFor_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    BasisFor S6_13409.table.semigroup.opposite (reversedBasis basis) :=
  (S6_13409.basisPair_of_derivationalCompleteness complete).opposite

/-- Unconditional representative and opposite endpoints for `S6_13403`. -/
theorem S6_13403.basisPair : TargetBasisPair S6_13403.table :=
  S6_13403.basisPair_of_derivationalCompleteness
    derivationalCompleteness

theorem S6_13403.representativeBasisFor :
    BasisFor S6_13403.table.semigroup basis :=
  S6_13403.basisPair.representative

theorem S6_13403.oppositeBasisFor :
    BasisFor S6_13403.table.semigroup.opposite (reversedBasis basis) :=
  S6_13403.basisPair.opposite

/-- Unconditional representative and opposite endpoints for `S6_13408`. -/
theorem S6_13408.basisPair : TargetBasisPair S6_13408.table :=
  S6_13408.basisPair_of_derivationalCompleteness
    derivationalCompleteness

theorem S6_13408.representativeBasisFor :
    BasisFor S6_13408.table.semigroup basis :=
  S6_13408.basisPair.representative

theorem S6_13408.oppositeBasisFor :
    BasisFor S6_13408.table.semigroup.opposite (reversedBasis basis) :=
  S6_13408.basisPair.opposite

/-- Unconditional representative and opposite endpoints for `S6_13409`. -/
theorem S6_13409.basisPair : TargetBasisPair S6_13409.table :=
  S6_13409.basisPair_of_derivationalCompleteness
    derivationalCompleteness

theorem S6_13409.representativeBasisFor :
    BasisFor S6_13409.table.semigroup basis :=
  S6_13409.basisPair.representative

theorem S6_13409.oppositeBasisFor :
    BasisFor S6_13409.table.semigroup.opposite (reversedBasis basis) :=
  S6_13409.basisPair.opposite

/-- All representative and opposite endpoints generated from the one shared
unrestricted theorem. -/
theorem signature4TargetBasisPairs_of_derivationalCompleteness
    (complete : DerivationalCompleteness) :
    TargetBasisPair S6_13403.table ∧
      TargetBasisPair S6_13408.table ∧
        TargetBasisPair S6_13409.table :=
  ⟨S6_13403.basisPair_of_derivationalCompleteness complete,
    S6_13408.basisPair_of_derivationalCompleteness complete,
    S6_13409.basisPair_of_derivationalCompleteness complete⟩

/-- Unconditional aggregate for all three representatives and opposites. -/
theorem signature4TargetBasisPairs :
    TargetBasisPair S6_13403.table ∧
      TargetBasisPair S6_13408.table ∧
        TargetBasisPair S6_13409.table :=
  ⟨S6_13403.basisPair, S6_13408.basisPair, S6_13409.basisPair⟩

end SemigroupBasis.CoRoots.Order6LeeA2LatticeScaffold
