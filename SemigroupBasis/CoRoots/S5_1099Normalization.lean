import SemigroupBasis.CoRoots.S5_1099
import SemigroupBasis.Examples.LeftRegularBandThree
import SemigroupBasis.Nonfinite.GraphParity

namespace SemigroupBasis.CoRoots.S5_1099

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev wordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

/-- State of the deterministic introduction-trace scanner. `core` is a
connected walk containing every variable seen so far, and `final` is the
last scanned variable. -/
structure TraceState where
  core : List Nat
  final : Nat
deriving Repr, DecidableEq

def traceStep (state : TraceState) (next : Nat) : TraceState :=
  if next ∈ state.core then
    ⟨state.core, next⟩
  else
    ⟨state.core ++ [state.final, next], next⟩

def traceState (word : Word Nat) : TraceState :=
  word.tail.foldl traceStep ⟨[word.head], word.head⟩

def traceNormalList (word : Word Nat) : List Nat :=
  (traceState word).core ++ [(traceState word).final]

def traceNormalWord (word : Word Nat) : Word Nat :=
  match traceNormalList word with
  | [] => Word.singleton word.head
  | head :: tail => wordOfCons head tail

private theorem traceStep_final_mem
    (state : TraceState) (stateFinal : state.final ∈ state.core)
    (next : Nat) :
    (traceStep state next).final ∈ (traceStep state next).core := by
  by_cases member : next ∈ state.core
  · simp [traceStep, member]
  · simp [traceStep, member]

private theorem traceFold_final_mem
    (state : TraceState) (stateFinal : state.final ∈ state.core) :
    ∀ letters : List Nat,
      (letters.foldl traceStep state).final ∈
        (letters.foldl traceStep state).core
  | [] => stateFinal
  | next :: rest => by
      simp only [List.foldl_cons]
      exact traceFold_final_mem
        (traceStep state next)
        (traceStep_final_mem state stateFinal next)
        rest

private theorem listDerivesHeadEdgeForward
    (head next : Nat) (rest terminalPrefix : List Nat) :
    ListDerives
      ((head :: next :: rest) ++ terminalPrefix ++ [head, next])
      ((head :: next :: rest) ++ terminalPrefix ++ [next]) := by
  cases gap : rest ++ terminalPrefix with
  | nil =>
      have square :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceContraction
            (wordOfCons head [next]))
      have duplicateNext :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceExpansion (Word.singleton next))
      have first :
          ListDerives [head, next, head, next] [head, next] := by
        simpa [wordOfCons, Word.append, Word.singleton] using square
      have second :
          ListDerives [head, next] [head, next, next] := by
        simpa [wordOfCons, Word.append, Word.singleton] using
          duplicateNext.prepend [head]
      simpa [gap, List.append_assoc] using first.trans second
  | cons gapHead gapTail =>
      have bridge :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          ((derivesForwardBridge
            (Word.singleton head)
            (Word.singleton next)
            (wordOfCons gapHead gapTail)).symm)
      simpa [gap, wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using bridge

private theorem listDerivesHeadEdgeReverse
    (head next : Nat) (rest terminalPrefix : List Nat) :
    ListDerives
      ((head :: next :: rest) ++ terminalPrefix ++ [next, head])
      ((head :: next :: rest) ++ terminalPrefix ++ [head]) := by
  cases gap : rest ++ terminalPrefix with
  | nil =>
      have adjacent :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceContraction (Word.singleton next))
      simpa [gap, wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.context
            [head] [head] adjacent)
  | cons gapHead gapTail =>
      have bridge :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          ((derivesReverseBridge
            (Word.singleton head)
            (Word.singleton next)
            (wordOfCons gapHead gapTail)).symm)
      simpa [gap, wordOfCons, Word.append, Word.singleton,
        List.append_assoc] using bridge

private theorem listDerivesHeadToMember
    (head : Nat) :
    ∀ (tail terminalPrefix : List Nat) (target : Nat),
      target ∈ head :: tail →
      ListDerives
        ((head :: tail) ++ terminalPrefix ++ [head, target])
        ((head :: tail) ++ terminalPrefix ++ [target])
  | [], terminalPrefix, target, member => by
      have targetEq : target = head := by simpa using member
      subst target
      have adjacent :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceContraction (Word.singleton head))
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.context
          ([head] ++ terminalPrefix) [] adjacent)
  | next :: rest, terminalPrefix, target, member => by
      by_cases targetHead : target = head
      · subst target
        have adjacent :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesIdempotenceContraction (Word.singleton head))
        simpa [List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.context
            ((head :: next :: rest) ++ terminalPrefix) [] adjacent)
      · have targetTail : target ∈ next :: rest := by
          simpa [targetHead] using member
        by_cases targetNext : target = next
        · subst target
          exact listDerivesHeadEdgeForward
            head next rest terminalPrefix
        · have targetRest : target ∈ next :: rest := targetTail
          have insertNext :=
            (listDerivesHeadToMember next rest
              (terminalPrefix ++ [head]) target targetRest).symm
          have eraseHead :=
            (listDerivesHeadEdgeForward
              head next rest terminalPrefix).append [target]
          have erasePath :=
            listDerivesHeadToMember next rest
              terminalPrefix target targetRest
          apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
          · simpa [List.append_assoc] using insertNext.prepend [head]
          · apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
            · simpa [List.append_assoc] using eraseHead
            · simpa [List.append_assoc] using erasePath.prepend [head]
termination_by
  tail => tail.length

private theorem listDerivesMemberToHead
    (head : Nat) :
    ∀ (tail terminalPrefix : List Nat) (source : Nat),
      source ∈ head :: tail →
      ListDerives
        ((head :: tail) ++ terminalPrefix ++ [source, head])
        ((head :: tail) ++ terminalPrefix ++ [head])
  | [], terminalPrefix, source, member => by
      have sourceEq : source = head := by simpa using member
      subst source
      have adjacent :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceContraction (Word.singleton head))
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.context
          ([head] ++ terminalPrefix) [] adjacent)
  | next :: rest, terminalPrefix, source, member => by
      by_cases sourceHead : source = head
      · subst source
        have adjacent :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesIdempotenceContraction (Word.singleton head))
        simpa [List.append_assoc] using
          (SemigroupBasis.CoRoots.S5_107.ListDerives.context
            ((head :: next :: rest) ++ terminalPrefix) [] adjacent)
      · have sourceTail : source ∈ next :: rest := by
          simpa [sourceHead] using member
        by_cases sourceNext : source = next
        · subst source
          exact listDerivesHeadEdgeReverse
            head next rest terminalPrefix
        · have insertNext :=
            (listDerivesHeadEdgeReverse
              head next rest
              (terminalPrefix ++ [source])).symm
          have erasePath :=
            (listDerivesMemberToHead next rest
              terminalPrefix source sourceTail).append [head]
          have eraseNext :=
            listDerivesHeadEdgeReverse
              head next rest terminalPrefix
          apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
          · simpa [List.append_assoc] using insertNext
          · apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
            · simpa [List.append_assoc] using
                erasePath.prepend [head]
            · simpa [List.append_assoc] using eraseNext
termination_by
  tail => tail.length

/-- A connected prefix walk absorbs the penultimate member of any terminal
pair whose two letters already occur in that prefix. -/
theorem listDerivesTerminalDelete :
    ∀ (core terminalPrefix : List Nat) (source target : Nat),
      source ∈ core →
      target ∈ core →
      ListDerives
        (core ++ terminalPrefix ++ [source, target])
        (core ++ terminalPrefix ++ [target])
  | [], _, _, _, sourceMember, _ =>
      False.elim (by simpa using sourceMember)
  | head :: tail, terminalPrefix, source, target,
      sourceMember, targetMember => by
      by_cases sourceHead : source = head
      · subst source
        exact listDerivesHeadToMember
          head tail terminalPrefix target targetMember
      · have sourceTail : source ∈ tail := by
          simpa [sourceHead] using sourceMember
        by_cases targetHead : target = head
        · subst target
          exact listDerivesMemberToHead
            head tail terminalPrefix source sourceMember
        · have targetTail : target ∈ tail := by
            simpa [targetHead] using targetMember
          have recurse :=
            listDerivesTerminalDelete tail terminalPrefix
              source target sourceTail targetTail
          simpa [List.append_assoc] using recurse.prepend [head]
termination_by
  core => core.length

private theorem listDerivesTraceFold
    (state : TraceState) (stateFinal : state.final ∈ state.core) :
    ∀ letters : List Nat,
      ListDerives
        (state.core ++ [state.final] ++ letters)
        ((letters.foldl traceStep state).core ++
          [(letters.foldl traceStep state).final])
  | [] => by
      simpa using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (state.core ++ [state.final]))
  | next :: rest => by
      by_cases member : next ∈ state.core
      · have transition :=
          listDerivesTerminalDelete
            state.core [] state.final next stateFinal member
        have remaining :=
          listDerivesTraceFold
            (traceStep state next)
            (traceStep_final_mem state stateFinal next)
            rest
        apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
        · simpa [traceStep, member, List.append_assoc] using
            transition.append rest
        · simpa [traceStep, member, List.append_assoc] using remaining
      · have duplicate :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
            (derivesIdempotenceExpansion (Word.singleton next))
        have transition :=
          SemigroupBasis.CoRoots.S5_107.ListDerives.context
            (state.core ++ [state.final]) [] duplicate
        have remaining :=
          listDerivesTraceFold
            (traceStep state next)
            (traceStep_final_mem state stateFinal next)
            rest
        apply SemigroupBasis.CoRoots.S5_107.ListDerives.trans
        · simpa [traceStep, member, List.append_assoc] using
            transition.append rest
        · simpa [traceStep, member, Word.toList,
            List.append_assoc] using remaining
termination_by
  letters => letters.length

/-- Every word derives to its deterministic introduction-trace normal form. -/
theorem listDerivesTraceNormal (word : Word Nat) :
    ListDerives word.toList (traceNormalList word) := by
  cases word with
  | mk head tail =>
      let initial : TraceState := ⟨[head], head⟩
      have duplicate :=
        SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
          (derivesIdempotenceExpansion (Word.singleton head))
      have scan :=
        listDerivesTraceFold initial (by simp [initial]) tail
      simpa [traceNormalList, traceState, initial,
        List.append_assoc] using
          (duplicate.append tail).trans scan

theorem traceNormalList_ne_nil (word : Word Nat) :
    traceNormalList word ≠ [] := by
  simp [traceNormalList]

theorem derivesTraceNormal (word : Word Nat) :
    Derives basis word (traceNormalWord word) := by
  cases word with
  | mk wordHead wordTail =>
      have listDerivation :=
        listDerivesTraceNormal (Word.mk wordHead wordTail)
      cases normalEq : traceNormalList (Word.mk wordHead wordTail) with
      | nil =>
          exact False.elim
            (traceNormalList_ne_nil
              (Word.mk wordHead wordTail) normalEq)
      | cons head tail =>
          have nonemptyDerivation :
              ListDerives (wordHead :: wordTail) (head :: tail) := by
            simpa [Word.toList, normalEq] using listDerivation
          simpa [traceNormalWord, normalEq, wordOfCons] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.toWord
              nonemptyDerivation

/-- The variable immediately before the first occurrence of `target`.
`none` means that `target` is absent or initial. -/
def firstPredecessorFrom
    (previous target : Nat) : List Nat → Option Nat
  | [] => none
  | next :: rest =>
      if next = target then some previous
      else firstPredecessorFrom next target rest

def firstPredecessor (letters : List Nat) (target : Nat) : Option Nat :=
  match letters with
  | [] => none
  | head :: tail =>
      if head = target then none
      else firstPredecessorFrom head target tail

theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem firstOccurrenceSequence_append_singleton
    (selected : Nat) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters ++ [selected]) =
        if selected ∈ letters then
          firstOccurrenceSequence letters
        else
          firstOccurrenceSequence letters ++ [selected]
  | [] => by simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction :=
        firstOccurrenceSequence_append_singleton selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, member,
            List.filter_append]
      · have reverseEqual : selected ≠ letter := Ne.symm equal
        by_cases member : selected ∈ rest <;>
          simp [firstOccurrenceSequence, induction, equal, reverseEqual,
            member, List.filter_append]

private theorem firstPredecessorFrom_append_singleton_of_mem
    (target next : Nat) :
    ∀ (previous : Nat) (letters : List Nat),
      target ∈ letters →
        firstPredecessorFrom previous target (letters ++ [next]) =
          firstPredecessorFrom previous target letters
  | _, [], member => False.elim (by simpa using member)
  | previous, letter :: rest, member => by
      by_cases equal : letter = target
      · subst letter
        simp [firstPredecessorFrom]
      · have targetLetter : target ≠ letter := Ne.symm equal
        have restMember : target ∈ rest := by
          simpa [targetLetter] using member
        simp [firstPredecessorFrom, equal,
          firstPredecessorFrom_append_singleton_of_mem
            target next letter rest restMember]

private theorem firstPredecessor_append_singleton_of_mem
    (target next : Nat) :
    ∀ letters : List Nat,
      target ∈ letters →
        firstPredecessor (letters ++ [next]) target =
          firstPredecessor letters target
  | [], member => False.elim (by simpa using member)
  | head :: tail, member => by
      by_cases equal : head = target
      · subst head
        simp [firstPredecessor]
      · have targetHead : target ≠ head := Ne.symm equal
        have tailMember : target ∈ tail := by
          simpa [targetHead] using member
        simp [firstPredecessor, equal,
          firstPredecessorFrom_append_singleton_of_mem
            target next head tail tailMember]

private theorem firstPredecessorFrom_append_target_of_not_mem
    (target : Nat) :
    ∀ (previous : Nat) (letters : List Nat),
      target ∉ letters →
        firstPredecessorFrom previous target (letters ++ [target]) =
          some (letters.getLastD previous)
  | previous, [], _ => by
      simp [firstPredecessorFrom]
  | previous, letter :: rest, absent => by
      have letterNe : letter ≠ target := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : target ∉ rest := fun member =>
        absent (List.Mem.tail letter member)
      have lastIndependent :
          rest.getLastD letter =
            (letter :: rest).getLastD previous := by
        rw [List.getLastD_cons]
      have lastIndependentOption :
          rest.getLast?.getD letter =
            (letter :: rest).getLast?.getD previous := by
        simpa only [List.getLastD_eq_getLast?] using lastIndependent
      simp [firstPredecessorFrom, letterNe, lastIndependentOption,
        firstPredecessorFrom_append_target_of_not_mem
          target letter rest restAbsent]

private theorem firstPredecessor_append_singleton_of_not_mem
    (head target : Nat) (tail : List Nat)
    (absent : target ∉ head :: tail) :
    firstPredecessor (head :: (tail ++ [target])) target =
      some (tail.getLastD head) := by
  have headNe : head ≠ target := by
    intro equal
    subst head
    exact absent (List.Mem.head tail)
  have tailAbsent : target ∉ tail := fun member =>
    absent (List.Mem.tail head member)
  simp [firstPredecessor, headNe,
    firstPredecessorFrom_append_target_of_not_mem
      target head tail tailAbsent]

private theorem flatMap_congr_of_mem
    (leftBlock rightBlock : Nat → List Nat) :
    ∀ letters : List Nat,
      (∀ letter ∈ letters,
        leftBlock letter = rightBlock letter) →
      letters.flatMap leftBlock = letters.flatMap rightBlock
  | [], _ => rfl
  | letter :: rest, same => by
      rw [List.flatMap_cons, List.flatMap_cons,
        same letter (by simp)]
      exact congrArg (fun suffix => rightBlock letter ++ suffix) <|
        flatMap_congr_of_mem leftBlock rightBlock rest <| by
          intro selected member
          exact same selected (by simp [member])

private def traceEdge
    (predecessor : Nat → Option Nat) (target : Nat) : List Nat :=
  match predecessor target with
  | none => []
  | some previous => [previous, target]

private def traceCoreOf
    (sequence : List Nat)
    (predecessor : Nat → Option Nat) : List Nat :=
  match sequence with
  | [] => []
  | head :: rest => head :: rest.flatMap (traceEdge predecessor)

private theorem traceCoreOf_append_singleton
    (head next : Nat) (tail : List Nat) :
    traceCoreOf
        (firstOccurrenceSequence (head :: (tail ++ [next])))
        (fun target =>
          firstPredecessor (head :: (tail ++ [next])) target) =
      if next ∈ head :: tail then
        traceCoreOf
          (firstOccurrenceSequence (head :: tail))
          (fun target => firstPredecessor (head :: tail) target)
      else
        traceCoreOf
            (firstOccurrenceSequence (head :: tail))
            (fun target => firstPredecessor (head :: tail) target) ++
          [tail.getLastD head, next] := by
  change
    traceCoreOf
        (firstOccurrenceSequence ((head :: tail) ++ [next]))
        (fun target =>
          firstPredecessor ((head :: tail) ++ [next]) target) = _
  by_cases nextMember : next ∈ head :: tail
  · simp only [firstOccurrenceSequence_append_singleton,
      if_pos nextMember]
    cases sequenceEq : firstOccurrenceSequence (head :: tail) with
    | nil => rfl
    | cons first rest =>
        have edgesEqual :
            rest.flatMap
                (traceEdge (fun target =>
                  firstPredecessor ((head :: tail) ++ [next]) target)) =
              rest.flatMap
                (traceEdge (fun target =>
                  firstPredecessor (head :: tail) target)) := by
          apply flatMap_congr_of_mem
          intro target targetMember
          have targetInSequence :
              target ∈ firstOccurrenceSequence (head :: tail) := by
            rw [sequenceEq]
            exact List.Mem.tail first targetMember
          have targetInLetters : target ∈ head :: tail :=
            (mem_firstOccurrenceSequence_iff target (head :: tail)).mp
              targetInSequence
          simp only [traceEdge]
          rw [firstPredecessor_append_singleton_of_mem
            target next (head :: tail) targetInLetters]
        simp only [traceCoreOf]
        exact congrArg (List.cons first) edgesEqual
  · simp only [firstOccurrenceSequence_append_singleton,
      if_neg nextMember]
    cases sequenceEq : firstOccurrenceSequence (head :: tail) with
    | nil =>
        have nonempty :
            firstOccurrenceSequence (head :: tail) ≠ [] := by
          simp [firstOccurrenceSequence]
        exact False.elim (nonempty sequenceEq)
    | cons first rest =>
        have edgesEqual :
            rest.flatMap
                (traceEdge (fun target =>
                  firstPredecessor ((head :: tail) ++ [next]) target)) =
              rest.flatMap
                (traceEdge (fun target =>
                  firstPredecessor (head :: tail) target)) := by
          apply flatMap_congr_of_mem
          intro target targetMember
          have targetInSequence :
              target ∈ firstOccurrenceSequence (head :: tail) := by
            rw [sequenceEq]
            exact List.Mem.tail first targetMember
          have targetInLetters : target ∈ head :: tail :=
            (mem_firstOccurrenceSequence_iff target (head :: tail)).mp
              targetInSequence
          simp only [traceEdge]
          rw [firstPredecessor_append_singleton_of_mem
            target next (head :: tail) targetInLetters]
        have nextEdge :
            traceEdge
                (fun target =>
                  firstPredecessor ((head :: tail) ++ [next]) target)
                next =
              [tail.getLastD head, next] := by
          simp only [traceEdge]
          rw [show
            firstPredecessor ((head :: tail) ++ [next]) next =
                some (tail.getLastD head) by
              simpa only [List.cons_append] using
                firstPredecessor_append_singleton_of_not_mem
                  head next tail nextMember]
        simp only [List.cons_append] at edgesEqual nextEdge
        simp only [sequenceEq, List.cons_append, traceCoreOf,
          List.flatMap_append, List.flatMap_singleton]
        rw [edgesEqual, nextEdge]

@[simp]
private theorem getLastD_append_singleton
    (fallback next : Nat) :
    ∀ tail : List Nat, (tail ++ [next]).getLastD fallback = next
  | [] => by simp
  | letter :: rest => by
      simp only [List.cons_append, List.getLastD_cons]
      exact getLastD_append_singleton letter next rest

private theorem mem_traceStep_core_iff
    (state : TraceState) (stateFinal : state.final ∈ state.core)
    (next tested : Nat) :
    tested ∈ (traceStep state next).core ↔
      tested ∈ state.core ∨ tested = next := by
  by_cases nextMember : next ∈ state.core
  · simp only [traceStep, nextMember, ↓reduceIte]
    constructor
    · exact Or.inl
    · rintro (member | equal)
      · exact member
      · subst tested
        exact nextMember
  · simp only [traceStep, nextMember, ↓reduceIte]
    constructor
    · intro member
      rcases List.mem_append.mp member with member | suffixMember
      · exact Or.inl member
      · simp at suffixMember
        rcases suffixMember with equal | equal
        · subst tested
          exact Or.inl stateFinal
        · exact Or.inr equal
    · rintro (member | equal)
      · exact List.mem_append.mpr (Or.inl member)
      · subst tested
        exact List.mem_append.mpr (Or.inr (by simp))

private structure TraceFoldInvariant
    (head : Nat) (tail : List Nat) (state : TraceState) : Prop where
  coreEq :
    state.core =
      traceCoreOf
        (firstOccurrenceSequence (head :: tail))
        (fun target => firstPredecessor (head :: tail) target)
  finalEq : state.final = tail.getLastD head
  support : ∀ tested, tested ∈ state.core ↔ tested ∈ head :: tail
  finalMem : state.final ∈ state.core

private theorem traceFold_invariant (head : Nat) :
    ∀ (remaining processed : List Nat) (state : TraceState),
      TraceFoldInvariant head processed state →
        TraceFoldInvariant head (processed ++ remaining)
          (remaining.foldl traceStep state)
  | [], processed, state, invariant => by
      simpa using invariant
  | next :: rest, processed, state, invariant => by
      have stepSupport :=
        mem_traceStep_core_iff state invariant.finalMem next
      have stepInvariant :
          TraceFoldInvariant head (processed ++ [next])
            (traceStep state next) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · by_cases member : next ∈ state.core
          · have processedMember : next ∈ head :: processed :=
              (invariant.support next).mp member
            simp only [traceStep, member, ↓reduceIte]
            rw [traceCoreOf_append_singleton,
              if_pos processedMember]
            exact invariant.coreEq
          · have processedAbsent : next ∉ head :: processed :=
              fun present => member ((invariant.support next).mpr present)
            simp only [traceStep, member, ↓reduceIte]
            rw [traceCoreOf_append_singleton,
              if_neg processedAbsent, invariant.coreEq,
              invariant.finalEq]
        · by_cases member : next ∈ state.core <;>
            simp [traceStep, member, getLastD_append_singleton]
        · intro tested
          rw [stepSupport tested, invariant.support tested]
          simp [List.mem_append, or_assoc]
        · exact traceStep_final_mem state invariant.finalMem next
      have remainingInvariant :=
        traceFold_invariant head rest (processed ++ [next])
          (traceStep state next) stepInvariant
      simpa [List.append_assoc] using remainingInvariant

private theorem traceState_signature (word : Word Nat) :
    (traceState word).core =
        traceCoreOf
          (firstOccurrenceSequence word.toList)
          (fun target => firstPredecessor word.toList target) ∧
      (traceState word).final = word.final := by
  cases word with
  | mk head tail =>
      have initial :
          TraceFoldInvariant head [] ⟨[head], head⟩ := by
        refine ⟨?_, rfl, ?_, by simp⟩
        · simp [traceCoreOf, firstOccurrenceSequence]
        · intro tested
          simp
      have completed :=
        traceFold_invariant head tail [] ⟨[head], head⟩ initial
      constructor
      · simpa [traceState, Word.toList] using completed.coreEq
      · simpa [traceState, Word.final] using completed.finalEq

def SameTraceSignature (left right : Word Nat) : Prop :=
  firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList ∧
    (∀ target,
      firstPredecessor left.toList target =
        firstPredecessor right.toList target) ∧
    left.final = right.final

/-- The scan output is determined by first-occurrence order, every
first-occurrence predecessor, and the final variable. -/
theorem traceNormalList_eq_of_signature
    {left right : Word Nat}
    (same : SameTraceSignature left right) :
    traceNormalList left = traceNormalList right := by
  rcases same with ⟨firstEqual, predecessorEqual, finalEqual⟩
  have predecessorFunctionEqual :
      (fun target => firstPredecessor left.toList target) =
        fun target => firstPredecessor right.toList target :=
    funext predecessorEqual
  have leftState := traceState_signature left
  have rightState := traceState_signature right
  have coreEqual :
      (traceState left).core = (traceState right).core := by
    rw [leftState.1, rightState.1, firstEqual,
      predecessorFunctionEqual]
  have stateFinalEqual :
      (traceState left).final = (traceState right).final :=
    leftState.2.trans <| finalEqual.trans rightState.2.symm
  simp only [traceNormalList]
  rw [coreEqual, stateFinalEqual]

/-- Equal trace signatures are derivable by normalization. -/
theorem derives_of_sameTraceSignature
    {left right : Word Nat}
    (same : SameTraceSignature left right) :
    Derives basis left right := by
  have leftNormal := derivesTraceNormal left
  have rightNormal := derivesTraceNormal right
  have normalListEqual := traceNormalList_eq_of_signature same
  have normalWordEqual :
      traceNormalWord left = traceNormalWord right := by
    cases rightEq : traceNormalList right with
    | nil =>
        exact False.elim (traceNormalList_ne_nil right rightEq)
    | cons head tail =>
        have leftEq : traceNormalList left = head :: tail :=
          normalListEqual.trans rightEq
        simp [traceNormalWord, leftEq, rightEq]
  exact leftNormal.trans <| by
    rw [normalWordEqual]
    exact rightNormal.symm

end SemigroupBasis.CoRoots.S5_1099
