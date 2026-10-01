import SemigroupBasis.CoRoots.Order6LeeLiP2G5

/-!
# Lee--Li Proposition 2, group G5: finite separation bridge

The G5 normalizer proves that the law `xyx = yx` reduces every word to the
last-occurrence sequence, with the final letter repeated exactly when the
original word ends in a square.  This module closes the remaining generic
semantic step.

Any disagreement of those invariants survives a renaming into the fixed
three-letter alphabet `{0, 1, 2}`.  Consequently a concrete order-six member
needs only:

* a proof that it models `xyx = yx`; and
* a finite list of valuations whose fingerprints are duplicate-free on the
  shared 30-word canonical inventory.

No concrete multiplication table or member-specific certificate is stored in
this module.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G5.Injection

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiP2G5

private theorem invariant_ext {left right : Invariant}
    (lord : left.lord = right.lord)
    (finalSquare : left.finalSquare = right.finalSquare) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem lastOccurrenceSequence_cons (letter : Nat)
    (rest : List Nat) :
    lastOccurrenceSequence (letter :: rest) =
      if letter ∈ rest then
        lastOccurrenceSequence rest
      else
        letter :: lastOccurrenceSequence rest := by
  change
    SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence
        (letter :: rest) =
      if letter ∈ rest then
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence rest
      else
        letter ::
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence rest
  rw [SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence.eq_def]

private theorem lastOccurrenceSequence_mem_iff (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ lastOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by
      change selected ∈
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence [] ↔
        selected ∈ []
      rfl
  | letter :: rest => by
      rw [lastOccurrenceSequence_cons letter rest]
      by_cases later : letter ∈ rest
      · rw [if_pos later, lastOccurrenceSequence_mem_iff selected rest]
        constructor
        · intro member
          exact List.Mem.tail letter member
        · intro member
          rcases List.mem_cons.mp member with selectedEq | member
          · subst selected
            exact later
          · exact member
      · simp only [if_neg later, List.mem_cons,
          lastOccurrenceSequence_mem_iff selected rest]

private theorem lastOccurrenceSequence_nodup :
    ∀ letters : List Nat, (lastOccurrenceSequence letters).Nodup
  | [] => by
      change
        (SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence []).Nodup
      exact List.nodup_nil
  | letter :: rest => by
      rw [lastOccurrenceSequence_cons letter rest]
      by_cases later : letter ∈ rest
      · rw [if_pos later]
        exact lastOccurrenceSequence_nodup rest
      · rw [if_neg later, List.nodup_cons]
        exact ⟨fun member =>
          later ((lastOccurrenceSequence_mem_iff letter rest).1 member),
          lastOccurrenceSequence_nodup rest⟩

private theorem lastOccurrenceSequence_ne_nil {letters : List Nat}
    (nonempty : letters ≠ []) :
    lastOccurrenceSequence letters ≠ [] := by
  intro empty
  cases letters with
  | nil => contradiction
  | cons head tail =>
      have present : head ∈ lastOccurrenceSequence (head :: tail) :=
        (lastOccurrenceSequence_mem_iff head (head :: tail)).2 (by simp)
      rw [empty] at present
      simp at present

private theorem lastOccurrenceSequence_eq_self_of_nodup :
    ∀ {letters : List Nat}, letters.Nodup →
      lastOccurrenceSequence letters = letters
  | [], _ => by
      change
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence [] = []
      rfl
  | letter :: rest, nodup => by
      have absent : letter ∉ rest := (List.nodup_cons.mp nodup).1
      have tailNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
      rw [lastOccurrenceSequence_cons, if_neg absent,
        lastOccurrenceSequence_eq_self_of_nodup tailNodup]

private theorem lastOccurrenceSequence_filter (keep : Nat → Bool) :
    ∀ letters : List Nat,
      lastOccurrenceSequence (letters.filter keep) =
        (lastOccurrenceSequence letters).filter keep
  | [] => by
      change
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence [] =
          List.filter keep
            (SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence [])
      rfl
  | letter :: rest => by
      have induction := lastOccurrenceSequence_filter keep rest
      by_cases kept : keep letter
      · by_cases member : letter ∈ rest
        · have filteredMember : letter ∈ rest.filter keep := by
            simp [member, kept]
          simp [lastOccurrenceSequence_cons, kept, member, filteredMember,
            induction]
        · have filteredAbsent : letter ∉ rest.filter keep := by
            simp [member]
          simp [lastOccurrenceSequence_cons, kept, member, filteredAbsent,
            induction]
      · by_cases member : letter ∈ rest
        · simp [lastOccurrenceSequence_cons, kept, member, induction]
        · simp [lastOccurrenceSequence_cons, kept, member, induction]

private theorem lastOccurrenceSequence_map_reduce (sigma : Nat → Nat) :
    ∀ letters : List Nat,
      lastOccurrenceSequence (letters.map sigma) =
        lastOccurrenceSequence
          ((lastOccurrenceSequence letters).map sigma)
  | [] => by
      change
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence [] =
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence
            (List.map sigma
              (SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence []))
      rfl
  | letter :: rest => by
      simp only [List.map_cons]
      rw [lastOccurrenceSequence_cons letter rest]
      by_cases later : letter ∈ rest
      · have mappedLater : sigma letter ∈ rest.map sigma :=
          List.mem_map.mpr ⟨letter, later, rfl⟩
        rw [if_pos later]
        rw [lastOccurrenceSequence_cons (sigma letter) (rest.map sigma),
          if_pos mappedLater]
        exact
          lastOccurrenceSequence_map_reduce sigma rest
      · rw [if_neg later]
        simp only [List.map_cons]
        have imageLaterIff :
            sigma letter ∈ rest.map sigma ↔
              sigma letter ∈ (lastOccurrenceSequence rest).map sigma := by
          constructor
          · intro member
            rcases List.mem_map.mp member with ⟨source, sourceMem, sourceImage⟩
            exact List.mem_map.mpr
              ⟨source,
                (lastOccurrenceSequence_mem_iff source rest).2 sourceMem,
                sourceImage⟩
          · intro member
            rcases List.mem_map.mp member with ⟨source, sourceMem, sourceImage⟩
            exact List.mem_map.mpr
              ⟨source,
                (lastOccurrenceSequence_mem_iff source rest).1 sourceMem,
                sourceImage⟩
        by_cases imageLater : sigma letter ∈ rest.map sigma
        · have reducedLater :
              sigma letter ∈ (lastOccurrenceSequence rest).map sigma :=
            imageLaterIff.1 imageLater
          rw [lastOccurrenceSequence_cons (sigma letter) (rest.map sigma),
            if_pos imageLater,
            lastOccurrenceSequence_cons (sigma letter)
              ((lastOccurrenceSequence rest).map sigma),
            if_pos reducedLater]
          exact lastOccurrenceSequence_map_reduce sigma rest
        · have reducedAbsent :
              sigma letter ∉ (lastOccurrenceSequence rest).map sigma :=
            fun member => imageLater (imageLaterIff.2 member)
          rw [lastOccurrenceSequence_cons (sigma letter) (rest.map sigma),
            if_neg imageLater,
            lastOccurrenceSequence_cons (sigma letter)
              ((lastOccurrenceSequence rest).map sigma),
            if_neg reducedAbsent,
            lastOccurrenceSequence_map_reduce sigma rest]

private theorem filter_eq_singleton_of_nodup_mem (selected : Nat) :
    ∀ {letters : List Nat}, letters.Nodup → selected ∈ letters →
      letters.filter (fun letter => decide (letter = selected)) = [selected]
  | [], _, member => by simp at member
  | head :: tail, nodup, member => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases headEq : head = selected
      · subst head
        have selectedAbsent : selected ∉ tail := headAbsent
        have tailFilter :
            tail.filter (fun letter => decide (letter = selected)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter letterMem
          have letterNe : letter ≠ selected := by
            intro equal
            subst letter
            exact selectedAbsent letterMem
          simp [letterNe]
        simp [List.filter_cons, tailFilter]
      · have tailMember : selected ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with selectedHead | member
          · exact False.elim (headEq selectedHead.symm)
          · exact member
        have induction :=
          filter_eq_singleton_of_nodup_mem selected tailNodup tailMember
        simp [headEq, induction]

private theorem filter_pair_tail
    {first second : Nat} {letters : List Nat}
    (different : first ≠ second) (firstAbsent : first ∉ letters)
    (secondMember : second ∈ letters) (nodup : letters.Nodup) :
    letters.filter
        (fun letter => decide (letter = first ∨ letter = second)) =
      [second] := by
  have singleton :=
    filter_eq_singleton_of_nodup_mem second nodup secondMember
  calc
    letters.filter
        (fun letter => decide (letter = first ∨ letter = second)) =
        letters.filter (fun letter => decide (letter = second)) := by
          apply List.filter_congr
          intro letter member
          have notFirst : letter ≠ first := by
            intro equal
            subst letter
            exact firstAbsent member
          simp [notFirst]
    _ = [second] := singleton

/-- Distinct duplicate-free lists with the same support contain a pair whose
relative order is reversed. -/
private theorem exists_opposite_pair :
    ∀ {left right : List Nat},
      left.Nodup → right.Nodup →
      (∀ letter, letter ∈ left ↔ letter ∈ right) →
      left ≠ right →
      ∃ first second, first ≠ second ∧
        left.filter
            (fun letter => decide (letter = first ∨ letter = second)) =
          [first, second] ∧
        right.filter
            (fun letter => decide (letter = first ∨ letter = second)) =
          [second, first]
  | [], [], _, _, _, different => False.elim (different rfl)
  | [], head :: tail, _, _, sameSupport, _ => by
      have impossible := (sameSupport head).2 (by simp)
      simp at impossible
  | head :: tail, [], _, _, sameSupport, _ => by
      have impossible := (sameSupport head).1 (by simp)
      simp at impossible
  | head :: tail, other :: rest, leftNodup, rightNodup,
      sameSupport, different => by
      have headAbsent := (List.nodup_cons.mp leftNodup).1
      have tailNodup := (List.nodup_cons.mp leftNodup).2
      have otherAbsent := (List.nodup_cons.mp rightNodup).1
      have restNodup := (List.nodup_cons.mp rightNodup).2
      by_cases headsEqual : head = other
      · subst other
        have tailSupport :
            ∀ letter, letter ∈ tail ↔ letter ∈ rest := by
          intro letter
          constructor
          · intro member
            have full : letter = head ∨ letter ∈ rest :=
              List.mem_cons.mp
                ((sameSupport letter).1 (List.Mem.tail head member))
            rcases full with letterEq | member
            · exact False.elim (headAbsent (letterEq ▸ member))
            · exact member
          · intro member
            have full : letter = head ∨ letter ∈ tail :=
              List.mem_cons.mp
                ((sameSupport letter).2 (List.Mem.tail head member))
            rcases full with letterEq | member
            · exact False.elim (otherAbsent (letterEq ▸ member))
            · exact member
        have tailsDifferent : tail ≠ rest := by
          intro equal
          apply different
          simp [equal]
        obtain ⟨first, second, pairNe, leftProjection, rightProjection⟩ :=
          exists_opposite_pair tailNodup restNodup tailSupport tailsDifferent
        have firstTail : first ∈ tail := by
          have kept : first ∈
              tail.filter
                (fun letter =>
                  decide (letter = first ∨ letter = second)) := by
            rw [leftProjection]
            simp
          exact (List.mem_filter.mp kept).1
        have secondTail : second ∈ tail := by
          have kept : second ∈
              tail.filter
                (fun letter =>
                  decide (letter = first ∨ letter = second)) := by
            rw [leftProjection]
            simp
          exact (List.mem_filter.mp kept).1
        have headNeFirst : head ≠ first := by
          intro equal
          subst first
          exact headAbsent firstTail
        have headNeSecond : head ≠ second := by
          intro equal
          subst second
          exact headAbsent secondTail
        refine ⟨first, second, pairNe, ?_, ?_⟩
        · simpa [List.filter_cons, headNeFirst, headNeSecond] using
            leftProjection
        · simpa [List.filter_cons, headNeFirst, headNeSecond] using
            rightProjection
      · have otherInTail : other ∈ tail := by
          have full : other ∈ head :: tail :=
            (sameSupport other).2 (by simp)
          exact (List.mem_cons.mp full).resolve_left (Ne.symm headsEqual)
        have headInRest : head ∈ rest := by
          have full : head ∈ other :: rest :=
            (sameSupport head).1 (by simp)
          exact (List.mem_cons.mp full).resolve_left headsEqual
        have leftTailProjection :=
          filter_pair_tail headsEqual headAbsent otherInTail tailNodup
        have rightTailProjection :=
          filter_pair_tail (Ne.symm headsEqual) otherAbsent headInRest
            restNodup
        have rightTailProjection' :
            rest.filter
                (fun letter => decide (letter = head ∨ letter = other)) =
              [head] := by
          calc
            rest.filter
                (fun letter => decide (letter = head ∨ letter = other)) =
                rest.filter
                  (fun letter => decide (letter = other ∨ letter = head)) := by
                    apply List.filter_congr
                    intro letter _
                    simp [or_comm]
            _ = [head] := rightTailProjection
        refine ⟨head, other, headsEqual, ?_, ?_⟩
        · simpa [List.filter_cons, headsEqual] using leftTailProjection
        · simpa [List.filter_cons, headsEqual, Ne.symm headsEqual] using
            rightTailProjection'

private def collapseAt (chosen letter : Nat) : Nat :=
  if letter = chosen then 1 else 0

private theorem collapseAt_bound (chosen letter : Nat) :
    collapseAt chosen letter <= 2 := by
  unfold collapseAt
  split <;> omega

private theorem collapseAt_fiber (chosen letter : Nat)
    (image : collapseAt chosen letter = 1) :
    letter = chosen := by
  by_cases equal : letter = chosen
  · exact equal
  · simp [collapseAt, equal] at image

private def separatePair (first second letter : Nat) : Nat :=
  if letter = first then 1 else if letter = second then 2 else 0

private theorem separatePair_bound (first second letter : Nat) :
    separatePair first second letter <= 2 := by
  unfold separatePair
  split
  · omega
  · split <;> omega

private theorem filter_map_separatePair
    (first second : Nat) (different : first ≠ second) :
    ∀ letters : List Nat,
      (letters.map (separatePair first second)).filter
          (fun image => decide (image = 1 ∨ image = 2)) =
        (letters.filter
          (fun letter => decide (letter = first ∨ letter = second))).map
            (separatePair first second)
  | [] => by simp
  | letter :: rest => by
      have induction :=
        filter_map_separatePair first second different rest
      simp only [List.map_cons, List.filter_cons]
      rw [induction]
      by_cases firstEq : letter = first
      · subst letter
        simp [separatePair]
      · by_cases secondEq : letter = second
        · subst letter
          simp [separatePair, firstEq]
        · simp [separatePair, firstEq, secondEq]

private theorem lord_pair_projection
    {letters : List Nat} {first second : Nat}
    (different : first ≠ second)
    (projection :
      letters.filter
          (fun letter => decide (letter = first ∨ letter = second)) =
        [first, second]) :
    (lastOccurrenceSequence
        (letters.map (separatePair first second))).filter
          (fun image => decide (image = 1 ∨ image = 2)) =
      [1, 2] := by
  rw [← lastOccurrenceSequence_filter]
  rw [filter_map_separatePair first second different]
  rw [projection]
  simp [lastOccurrenceSequence_cons, separatePair, different,
    Ne.symm different,
    SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence.eq_def]

private theorem lord_pair_projection_reverse
    {letters : List Nat} {first second : Nat}
    (different : first ≠ second)
    (projection :
      letters.filter
          (fun letter => decide (letter = first ∨ letter = second)) =
        [second, first]) :
    (lastOccurrenceSequence
        (letters.map (separatePair first second))).filter
          (fun image => decide (image = 1 ∨ image = 2)) =
      [2, 1] := by
  rw [← lastOccurrenceSequence_filter]
  rw [filter_map_separatePair first second different]
  rw [projection]
  simp [lastOccurrenceSequence_cons, separatePair, different,
    Ne.symm different,
    SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence.eq_def]

/-- Any disagreement of last-occurrence words survives a renaming whose image
is contained in `{0, 1, 2}`. -/
theorem lord_mergeCollapse {left right : List Nat}
    (different :
      lastOccurrenceSequence left ≠ lastOccurrenceSequence right) :
    ∃ sigma : Nat → Nat,
      (∀ letter, sigma letter <= 2) ∧
      lastOccurrenceSequence (left.map sigma) ≠
        lastOccurrenceSequence (right.map sigma) := by
  classical
  let leftLord := lastOccurrenceSequence left
  let rightLord := lastOccurrenceSequence right
  by_cases sameSupport :
      ∀ letter, letter ∈ leftLord ↔ letter ∈ rightLord
  · obtain ⟨first, second, pairNe, leftProjection, rightProjection⟩ :=
      exists_opposite_pair
        (lastOccurrenceSequence_nodup left)
        (lastOccurrenceSequence_nodup right)
        sameSupport different
    let sigma := separatePair first second
    refine ⟨sigma, fun letter => separatePair_bound first second letter, ?_⟩
    have leftKept := lord_pair_projection pairNe leftProjection
    have rightKept := lord_pair_projection_reverse pairNe rightProjection
    intro mappedEqual
    have reducedEqual :
        lastOccurrenceSequence (leftLord.map sigma) =
          lastOccurrenceSequence (rightLord.map sigma) := by
      rw [← lastOccurrenceSequence_map_reduce sigma left,
        ← lastOccurrenceSequence_map_reduce sigma right]
      exact mappedEqual
    have keptEqual := congrArg
      (fun letters => letters.filter
        (fun image => decide (image = 1 ∨ image = 2))) reducedEqual
    simp only [leftLord, rightLord, sigma] at keptEqual
    rw [leftKept, rightKept] at keptEqual
    simp at keptEqual
  · obtain ⟨chosen, supportDiff⟩ :=
      Classical.not_forall.mp sameSupport
    by_cases chosenLeft : chosen ∈ leftLord
    · have chosenRight : chosen ∉ rightLord := by
        intro member
        exact supportDiff <| Iff.intro (fun _ => member) (fun _ => chosenLeft)
      let sigma := collapseAt chosen
      refine ⟨sigma, fun letter => collapseAt_bound chosen letter, ?_⟩
      intro mappedEqual
      have imageLeft : 1 ∈ lastOccurrenceSequence (left.map sigma) := by
        rw [lastOccurrenceSequence_mem_iff]
        rcases (lastOccurrenceSequence_mem_iff chosen left).1 chosenLeft with
          sourceMem
        exact List.mem_map.mpr
          ⟨chosen, sourceMem, by simp [sigma, collapseAt]⟩
      have imageRight : 1 ∉ lastOccurrenceSequence (right.map sigma) := by
        rw [lastOccurrenceSequence_mem_iff]
        intro member
        rcases List.mem_map.mp member with
          ⟨source, sourceMem, sourceImage⟩
        have sourceEq : source = chosen := by
          apply collapseAt_fiber chosen source
          simpa [sigma] using sourceImage
        subst source
        exact chosenRight
          ((lastOccurrenceSequence_mem_iff chosen right).2 sourceMem)
      exact imageRight (mappedEqual ▸ imageLeft)
    · have chosenRight : chosen ∈ rightLord := by
        by_cases member : chosen ∈ rightLord
        · exact member
        · exact False.elim <| supportDiff <|
            Iff.intro (fun present => False.elim (chosenLeft present))
              (fun present => False.elim (member present))
      let sigma := collapseAt chosen
      refine ⟨sigma, fun letter => collapseAt_bound chosen letter, ?_⟩
      intro mappedEqual
      have imageRight : 1 ∈ lastOccurrenceSequence (right.map sigma) := by
        rw [lastOccurrenceSequence_mem_iff]
        rcases (lastOccurrenceSequence_mem_iff chosen right).1 chosenRight with
          sourceMem
        exact List.mem_map.mpr
          ⟨chosen, sourceMem, by simp [sigma, collapseAt]⟩
      have imageLeft : 1 ∉ lastOccurrenceSequence (left.map sigma) := by
        rw [lastOccurrenceSequence_mem_iff]
        intro member
        rcases List.mem_map.mp member with
          ⟨source, sourceMem, sourceImage⟩
        have sourceEq : source = chosen := by
          apply collapseAt_fiber chosen source
          simpa [sigma] using sourceImage
        subst source
        exact chosenLeft
          ((lastOccurrenceSequence_mem_iff chosen left).2 sourceMem)
      exact imageLeft (mappedEqual.symm ▸ imageRight)

private theorem finalSquareBit_true_map (sigma : Nat → Nat) :
    ∀ {letters : List Nat}, finalSquareBit letters = true →
      finalSquareBit (letters.map sigma) = true
  | [], source => by simp [finalSquareBit] at source
  | [_], source => by simp [finalSquareBit] at source
  | [first, second], source => by
      have equal : first = second := by
        simpa [finalSquareBit] using of_decide_eq_true source
      subst second
      simp [finalSquareBit]
  | first :: second :: third :: rest, source => by
      simpa [finalSquareBit] using
        finalSquareBit_true_map sigma (letters := second :: third :: rest)
          source

private theorem finalSquareBit_false_merge :
    ∀ {letters : List Nat}, finalSquareBit letters = false →
      ∃ sigma : Nat → Nat,
        (∀ letter, sigma letter <= 2) ∧
        finalSquareBit (letters.map sigma) = false
  | [], _ => by
      refine ⟨fun _ => 0, by simp, ?_⟩
      simp [finalSquareBit]
  | [_], _ => by
      refine ⟨fun _ => 0, by simp, ?_⟩
      simp [finalSquareBit]
  | [first, second], source => by
      have different : first ≠ second := by
        intro equal
        subst second
        simp [finalSquareBit] at source
      let sigma := separatePair first second
      refine ⟨sigma, fun letter => separatePair_bound first second letter, ?_⟩
      simp [finalSquareBit, sigma, separatePair, different,
        Ne.symm different]
  | first :: second :: third :: rest, source => by
      obtain ⟨sigma, bounded, mappedFalse⟩ :=
        finalSquareBit_false_merge
          (letters := second :: third :: rest) source
      refine ⟨sigma, bounded, ?_⟩
      simpa [finalSquareBit] using mappedFalse

/-- Every G5 invariant disagreement survives a substitution into exactly the
fixed alphabet `{0, 1, 2}`. -/
theorem mergeCollapse {left right : Word Nat}
    (different : invariant left ≠ invariant right) :
    ∃ sigma : Nat → Nat,
      (∀ letter, sigma letter <= 2) ∧
      invariant (left.map sigma) ≠ invariant (right.map sigma) := by
  classical
  by_cases lordEqual :
      (invariant left).lord = (invariant right).lord
  · have squareDifferent :
        (invariant left).finalSquare ≠ (invariant right).finalSquare := by
      intro squareEqual
      apply different
      cases leftInvariant : invariant left
      cases rightInvariant : invariant right
      simp_all
    cases leftSquare : (invariant left).finalSquare with
    | false =>
        have rightSquare : (invariant right).finalSquare = true := by
          cases value : (invariant right).finalSquare
          · exact False.elim (squareDifferent (leftSquare.trans value.symm))
          · rfl
        obtain ⟨sigma, bounded, mappedLeftFalse⟩ :=
          finalSquareBit_false_merge
            (letters := left.toList) (by simpa [invariant] using leftSquare)
        have mappedRightTrue :=
          finalSquareBit_true_map sigma (letters := right.toList)
            (by simpa [invariant] using rightSquare)
        refine ⟨sigma, bounded, ?_⟩
        intro mappedEqual
        have squareEqual := congrArg Invariant.finalSquare mappedEqual
        change finalSquareBit (left.toList.map sigma) =
          finalSquareBit (right.toList.map sigma) at squareEqual
        rw [mappedLeftFalse, mappedRightTrue] at squareEqual
        cases squareEqual
    | true =>
        have rightSquare : (invariant right).finalSquare = false := by
          cases value : (invariant right).finalSquare
          · rfl
          · exact False.elim (squareDifferent (leftSquare.trans value.symm))
        obtain ⟨sigma, bounded, mappedRightFalse⟩ :=
          finalSquareBit_false_merge
            (letters := right.toList) (by simpa [invariant] using rightSquare)
        have mappedLeftTrue :=
          finalSquareBit_true_map sigma (letters := left.toList)
            (by simpa [invariant] using leftSquare)
        refine ⟨sigma, bounded, ?_⟩
        intro mappedEqual
        have squareEqual := congrArg Invariant.finalSquare mappedEqual
        change finalSquareBit (left.toList.map sigma) =
          finalSquareBit (right.toList.map sigma) at squareEqual
        rw [mappedLeftTrue, mappedRightFalse] at squareEqual
        cases squareEqual
  · obtain ⟨sigma, bounded, mappedLordDifferent⟩ :=
      lord_mergeCollapse (left := left.toList) (right := right.toList)
        (by simpa [invariant] using lordEqual)
    refine ⟨sigma, bounded, ?_⟩
    intro mappedEqual
    apply mappedLordDifferent
    exact congrArg Invariant.lord mappedEqual

/-! ## Canonical inventory -/

private def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => Word.mk head tail

private theorem wordOfList_toList {letters : List Nat}
    (nonempty : letters ≠ []) :
    (wordOfList letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

private def boundedLords : List (List Nat) :=
  [[0], [1], [2],
   [0, 1], [0, 2], [1, 0], [1, 2], [2, 0], [2, 1],
   [0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0],
   [2, 0, 1], [2, 1, 0]]

private def boundedLordsWithEmpty : List (List Nat) :=
  [] :: boundedLords

private theorem boundedLordsWithEmpty_complete :
    ∀ letters : List Nat,
      letters.Nodup →
      (∀ letter, letter ∈ letters → letter <= 2) →
      letters ∈ boundedLordsWithEmpty
  | [], _, _ => by simp [boundedLordsWithEmpty]
  | head :: tail, nodup, bounded => by
      have tailNodup := (List.nodup_cons.mp nodup).2
      have tailBounded : ∀ letter, letter ∈ tail → letter <= 2 := by
        intro letter member
        exact bounded letter (by simp [member])
      have headBounded : head <= 2 := bounded head (by simp)
      have tailComplete :=
        boundedLordsWithEmpty_complete tail tailNodup tailBounded
      simp [boundedLordsWithEmpty, boundedLords] at tailComplete
      rcases tailComplete with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [boundedLordsWithEmpty, boundedLords] at * <;> omega

private theorem boundedLords_complete {letters : List Nat}
    (nodup : letters.Nodup) (nonempty : letters ≠ [])
    (bounded : ∀ letter, letter ∈ letters → letter <= 2) :
    letters ∈ boundedLords := by
  have complete :=
    boundedLordsWithEmpty_complete letters nodup bounded
  simpa [boundedLordsWithEmpty, nonempty] using complete

/-- The exact 30 canonical G5 words over the fixed alphabet `{0, 1, 2}`. -/
def canonicalInventory : List (Word Nat) :=
  boundedLords.flatMap fun lord =>
    [wordOfList lord,
      wordOfList (lord ++ [lord.getLastD 0])]

private theorem lastOccurrenceSequence_append_final_duplicate :
    ∀ (head : Nat) (tail : List Nat),
      (head :: tail).Nodup →
      lastOccurrenceSequence
          ((head :: tail) ++ [(head :: tail).getLastD 0]) =
        head :: tail
  | head, [], _ => by
      change lastOccurrenceSequence [head, head] = [head]
      rw [lastOccurrenceSequence_cons,
        if_pos (by simp), lastOccurrenceSequence_cons,
        if_neg (by simp)]
      change head :: [] = [head]
      rfl
  | head, next :: rest, nodup => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      have finalUnchanged :
          (head :: next :: rest).getLastD 0 =
            (next :: rest).getLastD 0 := by
        simp only [List.getLastD_cons]
      have lastMember : (next :: rest).getLastD 0 ∈ next :: rest := by
        simpa only [List.getLastD_cons] using
          List.getLastD_mem_cons (l := rest) (a := next)
      have headNeLast : head ≠ (next :: rest).getLastD 0 := by
        intro equal
        apply headAbsent
        simpa [equal] using lastMember
      have headNotLater :
          head ∉ (next :: rest) ++ [(next :: rest).getLastD 0] := by
        intro member
        rcases List.mem_append.mp member with member | member
        · exact headAbsent member
        · exact headNeLast (by simpa using member)
      rw [finalUnchanged, List.cons_append, lastOccurrenceSequence_cons,
        if_neg headNotLater]
      exact congrArg (List.cons head)
        (lastOccurrenceSequence_append_final_duplicate next rest tailNodup)

private theorem finalSquareBit_nodup_false :
    ∀ {letters : List Nat}, letters.Nodup →
      finalSquareBit letters = false
  | [], _ => by rfl
  | [_], _ => by rfl
  | [first, second], nodup => by
      have different : first ≠ second := by
        intro equal
        subst second
        simpa using (List.nodup_cons.mp nodup).1
      simp [finalSquareBit, different]
  | first :: second :: third :: rest, nodup => by
      rw [finalSquareBit]
      exact finalSquareBit_nodup_false (List.nodup_cons.mp nodup).2

private theorem finalSquareBit_append_final_true :
    ∀ (head : Nat) (tail : List Nat),
      finalSquareBit
          ((head :: tail) ++ [(head :: tail).getLastD 0]) = true
  | head, [] => by simp [finalSquareBit]
  | head, next :: rest => by
      cases rest with
      | nil => simp [finalSquareBit]
      | cons third remainder =>
          simpa only [List.cons_append, List.getLastD_cons, finalSquareBit]
            using
              finalSquareBit_append_final_true next (third :: remainder)

private theorem invariant_canonical (word : Word Nat) :
    invariant (canonical word) = invariant word := by
  have lordNodup := lastOccurrenceSequence_nodup word.toList
  have wordNonempty : word.toList ≠ [] := by
    cases word
    simp [Word.toList]
  have lordNonempty :=
    lastOccurrenceSequence_ne_nil (letters := word.toList) wordNonempty
  apply invariant_ext
  · change lastOccurrenceSequence (canonical word).toList =
      lastOccurrenceSequence word.toList
    rw [canonical_toList]
    cases square : finalSquareBit word.toList with
    | false =>
        simp [canonicalList, invariant, square,
          lastOccurrenceSequence_eq_self_of_nodup lordNodup]
    | true =>
        cases lord : lastOccurrenceSequence word.toList with
        | nil => exact False.elim (lordNonempty lord)
        | cons head tail =>
            simpa [canonicalList, invariant, square, lord] using
              lastOccurrenceSequence_append_final_duplicate head tail
                (by simpa [lord] using lordNodup)
  · change finalSquareBit (canonical word).toList =
      finalSquareBit word.toList
    rw [canonical_toList]
    cases square : finalSquareBit word.toList with
    | false =>
        simpa [canonicalList, invariant, square] using
          finalSquareBit_nodup_false lordNodup
    | true =>
        cases lord : lastOccurrenceSequence word.toList with
        | nil => exact False.elim (lordNonempty lord)
        | cons head tail =>
            simpa [canonicalList, invariant, square, lord] using
              finalSquareBit_append_final_true head tail

private theorem mapped_letters_bound (sigma : Nat → Nat)
    (bounded : ∀ letter, sigma letter <= 2) (word : Word Nat) :
    ∀ letter, letter ∈ (word.map sigma).toList → letter <= 2 := by
  intro letter member
  change letter ∈ word.toList.map sigma at member
  rcases List.mem_map.mp member with ⟨source, _, rfl⟩
  exact bounded source

private theorem canonical_mem_inventory_of_bound (word : Word Nat)
    (bounded : ∀ letter, letter ∈ word.toList → letter <= 2) :
    canonical word ∈ canonicalInventory := by
  let lord := lastOccurrenceSequence word.toList
  have lordNodup : lord.Nodup := lastOccurrenceSequence_nodup word.toList
  have wordNonempty : word.toList ≠ [] := by
    cases word
    simp [Word.toList]
  have lordNonempty : lord ≠ [] :=
    lastOccurrenceSequence_ne_nil (letters := word.toList) wordNonempty
  have lordBounded : ∀ letter, letter ∈ lord → letter <= 2 := by
    intro letter member
    exact bounded letter ((lastOccurrenceSequence_mem_iff letter _).1 member)
  have lordMember :=
    boundedLords_complete lordNodup lordNonempty lordBounded
  rw [canonicalInventory, List.mem_flatMap]
  refine ⟨lord, lordMember, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  cases square : finalSquareBit word.toList with
  | false =>
      left
      apply Word.toList_injective
      rw [canonical_toList, wordOfList_toList lordNonempty]
      simp [canonicalList, invariant, square, lord]
  | true =>
      right
      apply Word.toList_injective
      rw [canonical_toList,
        wordOfList_toList (by simp [lordNonempty] :
          lord ++ [lord.getLastD 0] ≠ [])]
      simp [canonicalList, invariant, square, lord]

/-! ## Finite fingerprints and the global endpoint -/

def separatorValuation (values : List Nat) (letter : Nat) : Fin 6 :=
  ⟨values.getD letter 0 % 6, Nat.mod_lt _ (by decide)⟩

/-- Semantic values of one canonical word under a finite separator list. -/
def memberFingerprint (semigroup : Semigroup (Fin 6))
    (separatorValuations : List (List Nat)) (word : Word Nat) : List Nat :=
  separatorValuations.map fun values =>
    (semigroup.eval (separatorValuation values) word).val

private theorem map_injective_on_of_nodup
    {entries : List alpha} {project : alpha → beta}
    (mappedNodup : (entries.map project).Nodup)
    {left right : alpha}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries)
    (sameImage : project left = project right) :
    left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headAbsent, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · exfalso
        apply headAbsent
        rw [sameImage]
        exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      · exfalso
        apply headAbsent
        rw [← sameImage]
        exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
      · exact ih tailNodup leftMember rightMember

private theorem exists_separator_of_fingerprint_ne
    (semigroup : Semigroup (Fin 6))
    (separatorValuations : List (List Nat))
    {left right : Word Nat}
    (different :
      memberFingerprint semigroup separatorValuations left ≠
        memberFingerprint semigroup separatorValuations right) :
    ∃ values, values ∈ separatorValuations ∧
      semigroup.eval (separatorValuation values) left ≠
        semigroup.eval (separatorValuation values) right := by
  apply Classical.byContradiction
  intro noSeparator
  apply different
  unfold memberFingerprint
  apply List.map_congr_left
  intro values member
  by_cases sameValue :
      semigroup.eval (separatorValuation values) left =
        semigroup.eval (separatorValuation values) right
  · exact congrArg Fin.val sameValue
  · exact False.elim <| noSeparator <|
      ⟨values, member, sameValue⟩

/-- The finite-to-global G5 separation bridge.  The only class-specific
premises are the one-law model check and duplicate-free fingerprints on the
shared 30-word inventory. -/
theorem invariantSeparation_of_fingerprints
    (semigroup : Semigroup (Fin 6))
    (models : Models semigroup basis)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (canonicalInventory.map
        (memberFingerprint semigroup separatorValuations)).Nodup) :
    InvariantSeparation semigroup := by
  intro identity valid
  apply Classical.byContradiction
  intro invariantDifferent
  obtain ⟨sigma, bounded, separated⟩ :=
    mergeCollapse invariantDifferent
  have mappedValid : (identity.map sigma).SatisfiedBy semigroup :=
    Identity.satisfiedBy_map identity sigma semigroup valid
  have leftMember := canonical_mem_inventory_of_bound
    (identity.lhs.map sigma)
    (mapped_letters_bound sigma bounded identity.lhs)
  have rightMember := canonical_mem_inventory_of_bound
    (identity.rhs.map sigma)
    (mapped_letters_bound sigma bounded identity.rhs)
  have canonicalDifferent :
      canonical (identity.lhs.map sigma) ≠
        canonical (identity.rhs.map sigma) := by
    intro canonicalEqual
    apply separated
    have invariantEqual := congrArg invariant canonicalEqual
    rw [invariant_canonical, invariant_canonical] at invariantEqual
    exact invariantEqual
  have fingerprintsDifferent :
      memberFingerprint semigroup separatorValuations
          (canonical (identity.lhs.map sigma)) ≠
        memberFingerprint semigroup separatorValuations
          (canonical (identity.rhs.map sigma)) := by
    intro sameFingerprint
    apply canonicalDifferent
    exact map_injective_on_of_nodup fingerprintsNodup
      leftMember rightMember sameFingerprint
  obtain ⟨values, _, separatedValues⟩ :=
    exists_separator_of_fingerprint_ne semigroup separatorValuations
      fingerprintsDifferent
  have validValues :
      semigroup.eval (separatorValuation values) (identity.lhs.map sigma) =
        semigroup.eval (separatorValuation values) (identity.rhs.map sigma) := by
    simpa [Identity.map] using mappedValid (separatorValuation values)
  have leftSound := Derives.sound models
    (derivesCanonical (identity.lhs.map sigma))
    (separatorValuation values)
  have rightSound := Derives.sound models
    (derivesCanonical (identity.rhs.map sigma))
    (separatorValuation values)
  exact separatedValues
    (leftSound.symm.trans (validValues.trans rightSound))

/-- Reusable endpoint for every concrete G5 member. -/
theorem basisFor_of_fingerprints
    (semigroup : Semigroup (Fin 6))
    (models : Models semigroup basis)
    (separatorValuations : List (List Nat))
    (fingerprintsNodup :
      (canonicalInventory.map
        (memberFingerprint semigroup separatorValuations)).Nodup) :
    BasisFor semigroup basis :=
  basisForOfInvariantSeparation semigroup models
    (invariantSeparation_of_fingerprints semigroup models
      separatorValuations fingerprintsNodup)

end SemigroupBasis.CoRoots.Order6LeeLiP2G5.Injection
